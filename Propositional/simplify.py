from Propositional.derivations import *
from queue import PriorityQueue
import time
from memory_profiler import memory_usage

PL = parse_logical


class Diagnostics:
    def __init__(self, starting_proposition: Evaluable, simplification: Evaluable,
                 considerations: int = None,
                 number_pruned: int = None,
                 time_taken: float = None,
                 negate_flush_passes: int = None):
        self.starting_proposition = starting_proposition
        self.simplification = simplification
        self.considerations = considerations
        self.number_pruned = number_pruned
        self.time_taken = time_taken
        self.negate_flush_passes = negate_flush_passes

    @staticmethod
    def time_taken_formatter(seconds: float):
        if seconds >= 60 * 60 * 24:
            # days
            days = seconds // (60 * 60 * 24)
            days = int(days)
            return f"{days} days, " + Diagnostics.time_taken_formatter(seconds % (60 * 60 * 24))
        if seconds >= 60 * 60:
            # hours
            hours = seconds // (60 * 60)
            hours = int(hours)
            return f"{hours} hours, " + Diagnostics.time_taken_formatter(seconds % (60 * 60))
        if seconds >= 60:
            # minutes
            minutes = seconds // 60
            minutes = int(minutes)
            return f"{minutes} minutes, " + Diagnostics.time_taken_formatter(seconds % 60)
        else:
            # seconds
            return f"{seconds:.4} seconds."

    def __str__(self):
        representation = f"""
        Diagnostics
        ---------------
        Starting proposition: {self.starting_proposition}
        Ending proposition: {self.simplification}
        """
        if self.considerations is not None:
            representation += f"""
            Considered {self.considerations} propositions.
            """
        if self.number_pruned is not None:
            representation += f"""
            Pruned {self.number_pruned}.
            """
        if self.time_taken is not None:
            representation += f"""
            Took {Diagnostics.time_taken_formatter(self.time_taken)}
            """
        if self.negate_flush_passes is not None:
            representation += f"""
            Went  to {self.negate_flush_passes} connectives/atoms.
            """

        border = "+----------------"

        return f"{border}\n| " + "\n| ".join(
            [_.lstrip() for _ in representation.strip().split("\n") if _.strip() != ""]
        ).replace("| -", "+--") + f"\n{border}"


class Simplification:
    def __init__(self, proposition: Evaluable):
        self.proposition = proposition
        self.simplified = None
        self.diagnostics = None

    def simplify(self, verbose) -> Evaluable:
        pass

    @property
    def get_simplified(self, verbose=False):
        if self.simplified is None:
            self.simplified = self.simplify(verbose)

        return self.simplified


class BFS(Simplification):
    def __init__(self, proposition: Evaluable):
        super().__init__(proposition)
        self.diagnostics = None

    def simplify(self, verbose: Union[bool, str] = True,
                 filter_logically_equivalent: bool = False,
                 stop_at: bool = None) -> Evaluable:

        progress_bar = (verbose == 'progress bar')
        if progress_bar:
            verbose = False

        start_time = time.time()

        if issubclass(type(self.proposition), Atom):
            self.diagnostics = Diagnostics(
                starting_proposition=self.proposition,
                simplification=self.proposition,
                considerations=0,
                number_pruned=0,
                time_taken=time.time() - start_time
            )
            return self.proposition
        elif issubclass(type(self.proposition), LogicalConnective):
            atomics = self.proposition.atoms_contained()

            # make sure no duplicates

            lst = []
            names = []

            for atom in atomics:
                if atom.name not in names:
                    lst.append(atom)
                    names.append(atom.name)

            atomics = lst
        else:
            raise LogicalException("Proposition malformed.")
        self.proposition: LogicalConnective

        return_value = None

        t_init = time.time()

        from itertools import count
        unique = count()

        if verbose:
            print(f"Initial to consider: {self.proposition}")

        to_consider = PriorityQueue()

        dependant_vars = []

        for a in atomics:
            # need to ask if prop depends on 'a'
            independent = True
            for i in range(2 ** (len(atomics))):
                context = {}
                for a2 in range(len(atomics)):
                    context.update({atomics[a2]: i & 1 << a2 != 0})

                context.update({a: True})
                self.proposition.set_atom_truth_values(context)
                truth_values_a = bool(self.proposition)
                context.update({a: False})
                self.proposition.set_atom_truth_values(context)
                truth_values_not_a = bool(self.proposition)

                independent = independent and (truth_values_a == truth_values_not_a)

            if not independent:
                to_consider.put((len(str(a)), next(unique), a))
                dependant_vars.append(a)

        new_considerations = []

        expanded_props = []

        truth_values_hash = set()

        considered = 0
        pruned = 0

        for option in [Tautology(), Falsehood()]:
            if self.proposition.equiv(option):
                return_value = option
                #########
        # Print iterations progress
        def print_progress_bar(iteration, total, prefix='', suffix='', decimals=1,
                               length=100, fill='█', print_end=""):
            """
            Call in a loop to create terminal progress bar
            @params:
                iteration   - Required  : current iteration (Int)
                total       - Required  : total iterations (Int)
                prefix      - Optional  : prefix string (Str)
                suffix      - Optional  : suffix string (Str)
                decimals    - Optional  : positive number of decimals in percent complete (Int)
                length      - Optional  : character length of bar (Int)
                fill        - Optional  : bar fill character (Str)
                print_end   - Optional  : end character (e.g. "\r", "\r\n") (Str)
            """
            percent = ("{0:." + str(decimals) + "f}").format(
                100 * (iteration / float(total)))
            filled_length = int(length * iteration // total)
            bar = fill * filled_length + '-' * (length - filled_length)
            print(f'\r{prefix} |{bar}| {percent}% {suffix}', end=print_end)
            # Print New Line on Complete
            if iteration == total:
                print()

        if return_value is None:
            if progress_bar:
                print()

            while not to_consider.empty():
                t_start = time.time()
                # print([x[-1] for x in to_consider.queue])
                next_connective = to_consider.get()[-1]
                next_connective: Evaluable

                if progress_bar:
                    print_progress_bar(
                        iteration=len(str(next_connective)),
                        total=len(str(self.proposition))+1,
                        prefix='BFS',
                        suffix=f" / {considered = } (T={(time.time()-t_init):.8})"
                    )
                    #######

                next_connective.truth_hash(atomics, regen=True)

                if verbose:
                    print(next_connective.truth_table(atomics) ==
                          self.proposition.truth_table(atomics))

                considered += 1
                if verbose:
                    print(f"{considered = }", next_connective,
                          f"\tPruned {pruned} options. "
                          f"(T={time.time()-t_init})")

                if self.proposition.equiv(next_connective):
                    if verbose:
                        print(f"Considered {considered} statement(s), pruned {pruned} options.")
                    return_value = next_connective
                    break
                    #########

                else:
                    if verbose:
                        print(self.proposition.truth_table(atomics),
                              next_connective.truth_table(atomics), sep="\n")

                    dd = DirectDerivation(axioms=[self.proposition],
                                          consequence=next_connective,
                                          derivation=[])
                    ce = dd.get_counter_example()

                    if ce is None:
                        dd = DirectDerivation(axioms=[next_connective],
                                              consequence=self.proposition,
                                              derivation=[])
                        ce = dd.get_counter_example()

                    if verbose:
                        print(f"Propositions {self.proposition} and {next_connective} are not "
                              f"equivalent: {ce}")

                    if ce is None:
                        print(self.proposition, next_connective)
                        exit(0)

                t_equiv = time.time()

                # prevent double negations.
                if type(next_connective) != LogicalNot:
                    not_connective = LogicalNot(next_connective)
                    new_considerations.append(
                        (len(str(not_connective)), next(unique), not_connective)
                    )

                t_not = time.time()

                for other_term in expanded_props:  # !!!!!!! to_consider.queue [OLD]
                    for logical_connective in [LogicalAnd, LogicalOr, LogicalImplies, LogicalIff]:
                        lc1 = logical_connective(other_term, next_connective)
                        lc2 = logical_connective(next_connective, other_term)

                        if filter_logically_equivalent:
                            if not lc1.truth_hash(atomics) in truth_values_hash:
                                new_considerations.append((len(str(lc1)), next(unique), lc1))
                        else:
                            new_considerations.append((len(str(lc1)), next(unique), lc1))

                        # only non-commutative operation.
                        if logical_connective == LogicalImplies:
                            if filter_logically_equivalent:
                                if not lc2.truth_hash(atomics) in truth_values_hash:
                                    new_considerations.append((len(str(lc2)), next(unique), lc2))
                            else:
                                new_considerations.append((len(str(lc2)), next(unique), lc2))

                t_consider = time.time()

                num_considerations = 0

                for consideration in new_considerations:
                    if filter_logically_equivalent:
                        # filter out all tautologies and falsehoods. Essentially starting from null
                        if consideration[-1].equiv(Tautology()) or \
                                consideration[-1].equiv(Falsehood()):
                            pruned += 1
                            continue

                        # filter if need be
                        if set(dependant_vars) != set(consideration[-1].atoms_contained()):
                            if len(str(consideration[-1])) <= len(str(self.proposition)):
                                to_consider.put(consideration)
                                num_considerations += 1
                            else:
                                pruned += 1
                            continue

                        t_hash = consideration[-1].truth_hash(atomics)

                        if t_hash in truth_values_hash:
                            if verbose:
                                print("Hash found:", t_hash, consideration[-1])
                            contained = True
                        else:
                            truth_values_hash.add(t_hash)
                            contained = False

                        if not contained:
                            if len(str(consideration[-1])) < len(str(self.proposition)):
                                num_considerations += 1
                                to_consider.put(consideration)
                            else:
                                pruned += 1
                        else:
                            pruned += 1
                    else:
                        # no filtering.
                        if len(str(consideration[-1])) < len(str(self.proposition)):
                            num_considerations += 1
                            to_consider.put(consideration)
                        else:
                            pruned += 1

                t_filtered = time.time()

                if verbose:
                    print(
                        "Equiv:    T =", f"{(t_equiv - t_start):.4}", "seconds",
                        "\nNot:      T =", f"{(t_not - t_equiv):.4}", "seconds",
                        "\nConsider: T =", f"{(t_consider - t_not):.4}", "seconds",
                        "\nFiltered: T =", f"{(t_filtered - t_consider):.4}", "seconds",
                        (f"(avg: {((t_filtered - t_consider) / num_considerations):.4}"
                         if num_considerations != 0 else
                         f"(avg: 0.0")
                        + f" seconds per cons.) ||| {num_considerations} cons.)"
                    )

                if next_connective == stop_at:
                    return_value = stop_at
                    break
                    #############

                expanded_props.append(next_connective)
                new_considerations = []

        # in case we don't find anything.
        if return_value is None:
            return_value = self.proposition

        if progress_bar:
            print_progress_bar(
                iteration=len(str(self.proposition)),
                total=len(str(self.proposition)),
                prefix='BFS',
                suffix=f" / {considered = } (T={(time.time() - t_init):.8})"
            )
            #######
            print()

        self.diagnostics = Diagnostics(
            starting_proposition=self.proposition,
            simplification=return_value,
            considerations=considered,
            number_pruned=pruned,
            time_taken=time.time() - start_time
        )

        return return_value


class FlushNegation(Simplification):
    """
    Flush negations down to the atomic level.

    ¬(A → B) -> (A ∧ ¬B)
    ¬(A ∨ B) -> (¬A ∧ ¬B)
    ¬(A ∧ B) -> (¬A ∨ ¬B)
    ¬(A ↔ B) -> ((A ∧ ¬B) ∨ (¬A ∧ B))


    """
    def __init__(self, proposition: Evaluable):
        super().__init__(proposition)

    def flush_negation(self, proposition, negate=False, verbose=False) -> (Evaluable, int):
        # if negation, we're passing down a not into the proposition, otherwise just flush as usual

        if verbose:
            print(proposition, f"<-- {negate = }")

        if type(proposition) is Atom:
            # return ¬A if we're negating otherwise A
            return (LogicalNot(proposition) if negate else proposition), 1
        elif type(proposition) is LogicalNot:
            inside = proposition.components[0]
            # if negate is True, and is not, so flip negate to False,
            # and set proposition to inside
            # if negate is False, and is not, so flip negate to True,
            # and set proposition to inside
            negation, depth = self.flush_negation(inside, negate=not negate, verbose=verbose)
            return negation, depth + 1

        elif type(proposition) is LogicalAnd:
            a, b = proposition.components[:2]
            flush_a, depth_a = self.flush_negation(a, negate=negate, verbose=verbose)
            flush_b, depth_b = self.flush_negation(b, negate=negate, verbose=verbose)

            if negate:
                return LogicalOr(flush_a, flush_b), depth_a + depth_b + 1
            else:
                return LogicalAnd(flush_a, flush_b), depth_a + depth_b + 1

        elif type(proposition) is LogicalOr:
            a, b = proposition.components[:2]
            flush_a, depth_a = self.flush_negation(a, negate=negate, verbose=verbose)
            flush_b, depth_b = self.flush_negation(b, negate=negate, verbose=verbose)

            if negate:
                return LogicalAnd(flush_a, flush_b), depth_a + depth_b + 1
            else:
                return LogicalOr(flush_a, flush_b), depth_a + depth_b + 1

        elif type(proposition) is LogicalImplies:
            a, b = proposition.components[:2]
            flush_a, depth_a = self.flush_negation(a, negate=False, verbose=verbose)

            if negate:
                flush_negate_b, depth_b = self.flush_negation(b, negate=negate, verbose=verbose)
                return LogicalAnd(flush_a, flush_negate_b), depth_a + depth_b + 1
            else:
                flush_b, depth_b = self.flush_negation(b, negate=negate, verbose=verbose)
                return LogicalImplies(flush_a, flush_b), depth_a + depth_b + 1

        elif type(proposition) is LogicalIff:
            a, b = proposition.components[:2]

            # if negate, then these are
            flush_negate_a, depth_a_n = self.flush_negation(a, negate=negate, verbose=verbose)
            flush_a, depth_a = self.flush_negation(a, negate=False, verbose=verbose)
            flush_b, depth_b = self.flush_negation(b, negate=False, verbose=verbose)

            if negate:
                return LogicalIff(flush_negate_a, flush_b), depth_b + depth_a_n + 1
            else:
                return LogicalIff(flush_a, flush_b), depth_a + depth_b + 1

        # raise logical exception if ever reaches here
        raise LogicalException("Malformed proposition in search.")

    def simplify(self, verbose: Union[bool, str] = False) -> Evaluable:
        start_time = time.time()
        flushed_prop, flush_passes = self.flush_negation(self.proposition, verbose=verbose)

        self.diagnostics = Diagnostics(
            starting_proposition=self.proposition,
            simplification=flushed_prop,
            negate_flush_passes=flush_passes,
            time_taken=time.time() - start_time
        )

        return flushed_prop


if __name__ == '__main__':
    prop = PL("((A implies B) implies (B implies (C or D)))")

    # v = True, False, or 'progress bar'
    v = 'progress bar'
    memory = False
    other = True

    print("-"*50)
    print("Flush Negation")

    fn = FlushNegation(prop)
    fn.simplify(verbose=v)
    diagnostics = fn.diagnostics

    print(diagnostics)

    print("-"*50)
    print("No Filter BFS")

    fn_result = diagnostics.simplification

    bfs = BFS(prop)
    bfs.simplify(verbose=v, filter_logically_equivalent=False)
    diagnostics = bfs.diagnostics

    print(diagnostics)

    print("-"*50)
    print("Filtered BFS")

    bfs = BFS(prop)
    bfs.simplify(verbose=v, filter_logically_equivalent=True)
    diagnostics = bfs.diagnostics

    print(diagnostics)

    if memory:
        mem_usage = memory_usage(bfs.simplify)
        print(mem_usage)
