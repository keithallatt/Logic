#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""

@author: Keith Allatt
@version: 1.1
"""

from klogic.Propositional.derivations import *
from queue import PriorityQueue
import time
from itertools import count
import json


PL = parse_logical


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
    def __init__(self, proposition: Evaluable, atomics_bank=None):
        super().__init__(proposition)
        self.atomics_bank = atomics_bank
        self.diagnostics = None

    def simplify(self, verbose: Union[bool, str] = True,
                 stop_at: bool = None) -> Evaluable:

        progress_bar = (verbose == 'progress bar')
        if progress_bar:
            verbose = False

        _start_time = time.time()
        _atomics = None

        if issubclass(type(self.proposition), Atom):
            self.diagnostics = Diagnostics(
                starting_proposition=self.proposition,
                simplification=self.proposition,
                considerations=0,
                number_pruned=0,
                time_taken=time.time() - _start_time
            )
            return self.proposition
        elif issubclass(type(self.proposition), LogicalConnective):
            _atomics = self.proposition.atoms_contained()

            # make sure no duplicates

            lst = []
            names = []

            for atom in _atomics:
                if atom.name not in names:
                    lst.append(atom)
                    names.append(atom.name)

            _atomics = lst
        elif issubclass(type(self.proposition), Tautology):
            pass
        elif issubclass(type(self.proposition), Falsehood):
            pass
        else:
            raise LogicalException("Proposition malformed.")
        self.proposition: LogicalConnective

        return_value = None

        t_init = time.time()

        unique = count()

        if verbose:
            print(f"Initial to consider: {self.proposition}")

        to_consider = PriorityQueue()

        dependant_vars = []

        for option in [Tautology(), Falsehood()]:
            if self.proposition.equiv(option):
                return_value = option
                #########
                self.diagnostics = Diagnostics(
                    starting_proposition=self.proposition,
                    simplification=option,
                    considerations=0,
                    number_pruned=0,
                    time_taken=time.time() - _start_time
                )

                return return_value

        if _atomics is not None:
            for a in _atomics:
                # need to ask if prop depends on 'a'
                independent = True
                for i in range(2 ** (len(_atomics))):
                    context = {}
                    for a2 in range(len(_atomics)):
                        context.update({_atomics[a2]: i & 1 << a2 != 0})

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

        considered = 0
        pruned = 0

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

                next_connective.truth_hash(_atomics, regen=True)

                if verbose:
                    print(next_connective.truth_table(_atomics) ==
                          self.proposition.truth_table(_atomics))

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
                        print(self.proposition.truth_table(_atomics),
                              next_connective.truth_table(_atomics), sep="\n")

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
                        print("not equiv but no counter example either way.", self.proposition,
                              next_connective)
                        exit(0)

                t_equiv = time.time()

                # prevent double negations.
                if type(next_connective) != LOGICAL_CONNECTIVES['not']:
                    not_connective = LOGICAL_CONNECTIVES['not'](next_connective)
                    new_considerations.append(
                        (len(str(not_connective)), next(unique), not_connective)
                    )

                t_not = time.time()

                for other_term in expanded_props:  # !!!!!!! to_consider.queue [OLD]
                    for logical_connective in LOGICAL_CONNECTIVES.values():
                        if logical_connective == LOGICAL_CONNECTIVES['not']:
                            continue

                        lc1 = logical_connective(other_term, next_connective)
                        lc2 = logical_connective(next_connective, other_term)

                        new_considerations.append((len(str(lc1)), next(unique), lc1))

                        # only non-commutative operation.
                        if logical_connective == LOGICAL_CONNECTIVES['implies']:
                            new_considerations.append((len(str(lc2)), next(unique), lc2))

                t_consider = time.time()

                num_considerations = 0

                for consideration in new_considerations:
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
                if self.atomics_bank is not None:
                    self.atomics_bank: AtomicsBank
                    self.atomics_bank.add_prop(next_connective)

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
            time_taken=time.time() - _start_time
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
            return (LOGICAL_CONNECTIVES['not'](proposition) if negate else proposition), 1
        elif type(proposition) is LOGICAL_CONNECTIVES['not']:
            inside = proposition.components[0]
            # if negate is True, and is not, so flip negate to False,
            # and set proposition to inside
            # if negate is False, and is not, so flip negate to True,
            # and set proposition to inside
            negation, depth = self.flush_negation(inside, negate=not negate, verbose=verbose)
            return negation, depth + 1

        elif type(proposition) is LOGICAL_CONNECTIVES['and']:
            a, b = proposition.components[:2]
            flush_a, depth_a = self.flush_negation(a, negate=negate, verbose=verbose)
            flush_b, depth_b = self.flush_negation(b, negate=negate, verbose=verbose)

            if negate:
                return (flush_a | flush_b), depth_a + depth_b + 1
            else:
                return (flush_a & flush_b), depth_a + depth_b + 1

        elif type(proposition) is LOGICAL_CONNECTIVES['or']:
            a, b = proposition.components[:2]
            flush_a, depth_a = self.flush_negation(a, negate=negate, verbose=verbose)
            flush_b, depth_b = self.flush_negation(b, negate=negate, verbose=verbose)

            if negate:
                return (flush_a & flush_b), depth_a + depth_b + 1
            else:
                return (flush_a | flush_b), depth_a + depth_b + 1

        elif type(proposition) is LOGICAL_CONNECTIVES['implies']:
            a, b = proposition.components[:2]
            flush_a, depth_a = self.flush_negation(a, negate=False, verbose=verbose)

            if negate:
                flush_negate_b, depth_b = self.flush_negation(b, negate=negate, verbose=verbose)
                return (flush_a & flush_negate_b), depth_a + depth_b + 1
            else:
                flush_b, depth_b = self.flush_negation(b, negate=negate, verbose=verbose)
                return (flush_a >> flush_b), depth_a + depth_b + 1

        elif type(proposition) is LOGICAL_CONNECTIVES['iff']:
            a, b = proposition.components[:2]

            # if negate, then these are
            flush_negate_a, depth_a_n = self.flush_negation(a, negate=negate, verbose=verbose)
            flush_a, depth_a = self.flush_negation(a, negate=False, verbose=verbose)
            flush_b, depth_b = self.flush_negation(b, negate=False, verbose=verbose)

            if negate:
                return (flush_negate_a ^ flush_b), depth_b + depth_a_n + 1
            else:
                return (flush_a ^ flush_b), depth_a + depth_b + 1

        # raise logical exception if ever reaches here
        raise LogicalException("Malformed proposition in search.")

    def simplify(self, verbose: Union[bool, str] = False) -> Evaluable:
        _start_time = time.time()
        flushed_prop, flush_passes = self.flush_negation(self.proposition, verbose=verbose)

        self.diagnostics = Diagnostics(
            starting_proposition=self.proposition,
            simplification=flushed_prop,
            negate_flush_passes=flush_passes,
            time_taken=time.time() - _start_time
        )

        return flushed_prop


def gen_connective_from_truth_table(truth_table, atomics_bank=None):
    def make_conn(_lst, conn_name, fallback=Falsehood()):
        conn = LOGICAL_CONNECTIVES.get(conn_name)
        if conn is None:
            raise LogicalException("Can't find connective: "+str(conn_name))
        if len(_lst) == 0:
            return fallback
        if len(_lst) == 1:
            return _lst[0]
        m = len(_lst) // 2
        lhs, rhs = _lst[:m], _lst[m:]
        return conn(make_conn(lhs, conn_name), make_conn(rhs, conn_name))

    combos_make_true = []

    for tv in truth_table:
        if tv[1]:
            lst = [_[0] if _[1] else (~_[0]) for _ in tv[0]]
            connective = make_conn(lst, 'and')
            combos_make_true.append(connective)

    lc1 = make_conn(combos_make_true, 'and')

    bfs = BFS(lc1, atomics_bank=atomics_bank)
    bfs.simplify(verbose='progress bar')

    lc1_simp = bfs.diagnostics.simplification

    return lc1_simp


class GenerateLogical:
    def __init__(self, _atomics: list[Atom]):
        self.atomics = _atomics
        self.queue = PriorityQueue()
        self.seen = set()
        self.unique = count()
        for atom in _atomics:
            self.queue.put((len(atom.name), atom.name))

    def __iter__(self):
        return self

    def __next__(self):
        next_item = self.queue.get()
        next_connective = next_item[-1]
        if type(PL(next_connective)) is not LOGICAL_CONNECTIVES['not']:
            str_repr = f"(not {next_connective})"
            self.queue.put((len(str(PL(str_repr))), str_repr))
        for seen_item in self.seen:
            seen_connective = seen_item[-1]
            for logical_connective in LOGICAL_SYMBOLS.keys():
                if logical_connective != "not":
                    str_repr = f"({next_connective} {logical_connective} {seen_connective})"
                    self.queue.put((len(str(PL(str_repr))), str_repr))
            str_repr = f"({seen_connective} implies {next_connective})"
            self.queue.put((len(str(PL(str_repr))), str_repr))
        self.seen.add(next_item)
        return PL(next_connective)


class AtomicsBank:
    def __init__(self, _atomics, file_out=None):
        self.propositions = {}
        self.lowest_unfilled = 0
        self.atomics = _atomics
        self.file_out = file_out
        if self.file_out is not None:
            self.read_from_file()
        self.add_prop(Tautology())
        self.add_prop(Falsehood())
        for atom in self.atomics:
            self.add_prop(atom)

    def add_prop(self, evaluable: Evaluable):
        truth = evaluable.truth_table(atomics, regen=True)
        index = self.index_from_truth(truth)
        existing = self.propositions.get(index)

        if existing is not None:
            try:
                if len(str(existing)) <= len(str(evaluable)):
                    return None
            except TypeError:
                print(existing, evaluable)

        self.propositions.update({index: evaluable})

        while self.lowest_unfilled in self.propositions.keys():
            self.lowest_unfilled += 1

        return index

    @staticmethod
    def index_from_truth(truth_table):
        index = 0
        for tv in truth_table:
            index <<= 1
            if tv[1]:
                index += 1
        return index

    def truth_from_index(self, index):
        truth_table = Tautology().truth_table(self.atomics, regen=True)
        for i in range(len(truth_table) - 1, -1, -1):
            # i from back to beggining
            truth_table[i] = (truth_table[i][0], index & 1 == 1)
            index >>= 1
        return truth_table

    def is_full(self):
        # self.prune()
        max_value = 2 ** (2 ** len(self.atomics))
        return len(self.propositions) == max_value

    def size(self):
        return len(self.propositions)

    def capacity(self):
        return 2 ** (2 ** len(self.atomics))

    def closure(self):
        i = 0
        generated_last_round = None
        generated_this_round = []
        havent_run_yet = True
        while not self.is_full() or havent_run_yet:
            old_props = [(k, v) for k, v in self.propositions.items()]
            if generated_last_round is None:
                generated_last_round = old_props[::]

            # Logical Not case
            for index, prop in old_props:
                i += 1
                if self.is_full():
                    print_progress_bar(self.capacity() - 1, self.capacity(),
                                       suffix=f'{self.size()} / {self.capacity()} {i}')
                else:
                    print_progress_bar(self.size(), self.capacity(),
                                       suffix=f'{self.size()} / {self.capacity()} {i}')

                if self.is_full() and not havent_run_yet:
                    print()
                    return

                if type(prop) not in [Tautology, Falsehood]:
                    # T/F symbol useless
                    not_prop = LOGICAL_CONNECTIVES['not'](prop)
                    self.add_prop(not_prop)
                    generated_this_round.append((0, not_prop))

            for logical_connective in LOGICAL_CONNECTIVES.values():
                if logical_connective == LOGICAL_CONNECTIVES['not']:
                    continue

                for index1, prop1 in old_props:
                    for index2, prop2 in generated_last_round:
                        i += 1
                        if self.is_full():
                            print_progress_bar(self.capacity()-1, self.capacity(),
                                               suffix=f'{self.size()} / {self.capacity()} {i}')
                        else:
                            print_progress_bar(self.size(), self.capacity(),
                                               suffix=f'{self.size()} / {self.capacity()} {i}')

                        if type(prop1) in [Tautology, Falsehood]:
                            continue
                        if type(prop2) in [Tautology, Falsehood]:
                            continue

                        if logical_connective == LOGICAL_CONNECTIVES['implies']:
                            # second case
                            self.add_prop(prop2 >> prop1)
                            generated_this_round.append((0, prop2 >> prop1))
                        # general case
                        self.add_prop(logical_connective(prop1, prop2))
                        generated_this_round.append((0, logical_connective(prop1, prop2)))

            generated_last_round = generated_this_round[::]
            generated_this_round = []
            havent_run_yet = False
        print()

    def read_from_file(self):
        try:
            f = open(self.file_out, 'r')
            f.close()
        except FileNotFoundError:
            self.save_to_file()

        with open(self.file_out, 'r') as file:
            contents = file.read()
            propositions = json.loads(contents)
            self.propositions = {
                int(index_str): (Tautology() if str(pl) == 'True' else
                                 Falsehood() if str(pl) == 'False' else PL(pl))
                for index_str, pl in propositions.items()
            }

            self.lowest_unfilled = 0
            while self.lowest_unfilled in self.propositions.keys():
                self.lowest_unfilled += 1

    def save_to_file(self):
        if self.file_out is None:
            raise Exception("File null in save_to_file.")

        json_formatted_propositions = {}

        for index, proposition in self.propositions.items():
            if type(proposition) is Tautology:
                json_formatted_propositions.update({index: True})
            elif type(proposition) is Falsehood:
                json_formatted_propositions.update({index: False})
            elif type(proposition) is Atom:
                json_formatted_propositions.update({index: proposition.name})
            elif issubclass(type(proposition), LogicalConnective):
                json_formatted_propositions.update({index: proposition.pl_ify()})

        json_formatted_propositions = {
            k: json_formatted_propositions[k]
            for k in sorted(list(json_formatted_propositions.keys()))
        }

        with open(self.file_out, 'w') as file:
            file.write(json.dumps(json_formatted_propositions, indent=4))
            file.close()

    def __sizeof__(self):
        return super().__sizeof__() + self.propositions.__sizeof__() + self.atomics.__sizeof__()

    def __str__(self):
        banner = "+---------"
        return banner + "\n| ".join([""] + [
            str(index) + ": " + str(self.propositions[index])
            for index in sorted(self.propositions.keys())
        ]) + "\n" + banner


if __name__ == '__main__':
    num_variables = 2
    atomics = [PL(chr(ord("A") + i)) for i in range(num_variables)]
    ab = AtomicsBank(atomics)
    gl = GenerateLogical(atomics)

    start_time = time.time()
    time_last_addition = time.time()
    last_added = 'None'

    banner_label = "\u2502 Finding all simplest propositions using breadth first search. \u2502"
    bannerT = "\u250C" + "\u2500" * (len(banner_label)-2) + "\u2510"
    bannerB = "\u2514" + "\u2500" * (len(banner_label)-2) + "\u2518"

    loading = '█' * 5 + ' ' * 10

    finished = False
    transition = False
    last_index = "None"

    def ppb():
        global last_added
        global transition
        global time_last_addition
        global loading
        global last_index

        index_str = str(ab.add_prop(e))
        if index_str != 'None':
            last_index = index_str
            last_added = str(e)
            time_last_addition = time.time()

        while len(last_index) < 6:
            last_index += " "
        while len(last_added) < 15:
            last_added += " "

        time_str = f"{(time.time() - start_time):.5}"

        while len(time_str) < 10:
            time_str += " "

        time_str_since = f"{(time.time() - time_last_addition):.6}"

        while len(time_str_since) < 10:
            time_str_since += " "

        loading = loading[-1] + loading[:-1]

        if time.time() - time_last_addition > 15 and not transition:
            print("\nTransition to BFS approach.")
            transition = True

        print_progress_bar(ab.size(), ab.capacity(),
                           length=50,
                           prefix=f"Adding index {last_index}: T={time_str} "
                                  f"(T={time_str_since} since) {last_added}",
                           suffix=f" ({ab.size()}/{ab.capacity()}) ({loading}) {ab.__sizeof__()}")
        return ab.size() == ab.capacity()

    print()

    autosave_time_start = time.time()

    while not ab.is_full():
        if transition:
            key = ab.lowest_unfilled-1

            e = gen_connective_from_truth_table(ab.truth_from_index(ab.lowest_unfilled))
        else:
            e = next(gl)

        finished = ppb()

    if not finished:
        ppb()

    print(ab)
