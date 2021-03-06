from __future__ import annotations
from sortedcontainers import SortedDict
from Propositional.arguments import *
import re


class Derivation:
    def __init__(self, derivation_kind: str, axioms: list[Evaluable],
                 assumptions: list[Evaluable], consequence: Evaluable,
                 derivation: list[Union[Argument, Derivation, SubDerivation]]):
        self.derives = {}
        self.derivation_kind = derivation_kind
        self.axioms = axioms
        self.axioms.sort(key=lambda _: str(_))
        self.assumptions = assumptions
        self.consequence = consequence

        for step, i in zip(derivation, range(len(derivation))):
            if type(step) is SubDerivation:
                step: SubDerivation
                step.__init__(step.derivation, step.environment, step.consequence, parent=self)
            elif issubclass(type(step), Derivation):
                step: Derivation
                derivation[i] = SubDerivation(step, parent=self)

        self.derivation = derivation
        self.verify_number_at = None
        self._final_i = None

    def is_valid(self):
        return self.get_counter_example() is None

    def argument_complete(self):
        return "Q.E.D." in self.verify()

    def __str__(self):
        axioms = "; ".join([
            str(axiom) for axiom in self.axioms
        ])

        return " ".join([axioms, TRUTH_SYMBOLS['proves'], str(self.consequence)])
            
    def __repr__(self):
        return self.__str__()
    
    def get_counter_example(self):
        """ In logic, more precisely in deductive reasoning, an argument is valid if and only if
            it is takes a form that makes it impossible for the premises to be true and the
            conclusion nevertheless to be false.

            If there exists a counterexample to the validity of this derivation, then return it.
            Otherwise return None (a valid argument returns None).
            """

        def set_atoms_truth_value(logical_connective: Evaluable, context: SortedDict):
            if type(logical_connective) is Atom:
                try:
                    logical_connective: Atom

                    for c in context:
                        if c.name == logical_connective.name:
                            logical_connective.truth_value = context[c]
                except KeyError:
                    print(context)
                    for c in context.keys():
                        print(c == logical_connective)
                    print(logical_connective)

            else:
                for component in logical_connective.components:
                    set_atoms_truth_value(component, context)

        # need to create an atom bank.
        atom_bank = {
            # atoms and their truth values
        }

        propositions = []

        for axiom in self.axioms:
            propositions.append(axiom)
        for assumption in self.assumptions:
            propositions.append(assumption)
        propositions.append(self.consequence)

        while len(propositions) > 0:
            next_prop = propositions.pop()

            if type(next_prop) is Atom:
                if next_prop.name not in [str(atom) for atom in atom_bank.keys()]:
                    atom_bank.update({next_prop: False})
            else:
                propositions += list(next_prop.components)

        atom_ordered = SortedDict(atom_bank)

        num_atoms = len(atom_ordered)

        for i in range(2 ** num_atoms):
            for atom in range(num_atoms):
                atom_ordered[list(atom_ordered.keys())[atom]] = (i & (1 << atom) != 0)

            axioms_and_assumptions = True

            for axiom in self.axioms:
                set_atoms_truth_value(axiom, atom_ordered)
                axioms_and_assumptions = axioms_and_assumptions and bool(axiom)
            for assumption in self.assumptions:
                set_atoms_truth_value(assumption, atom_ordered)
                axioms_and_assumptions = axioms_and_assumptions and bool(assumption)

            set_atoms_truth_value(self.consequence, atom_ordered)
            valid = bool(self.consequence) or not axioms_and_assumptions

            if not valid:
                counter_example = ", ".join([
                    str(atom) if tv else str(~atom) for atom, tv in atom_ordered.items()
                ])
                counter_example = f"({counter_example})"

                return counter_example

        return None

    @property
    def line_end_number(self):
        return self._final_i

    def verify(self, verify_number_at=1, consequence_str=None, join_after=True):
        self.verify_number_at = verify_number_at

        counter = self.get_counter_example()
        if counter is not None and type(self) != IndirectDerivation:
            return None, None

        justification = []

        derivation_name_short = "".join([
            char.lower() for char in self.derivation_kind if char.isupper()
        ])

        environment = self.axioms[::] + self.assumptions[::]
        self.derives = {}
        i = verify_number_at
        verification = ""

        if not self.derivation:
            self.derivation = [Repeat(self.consequence)]

        for derivation_step in self.derivation:
            locations = []

            if type(derivation_step) is SubDerivation:
                for e in derivation_step.environment:
                    if e not in environment:
                        # illegal (needs tweaks)
                        # print("Component not in environment", e)
                        justification.append(["Illegal Operation ?? " + str(e), "xx"])
                        self._final_i = i
                        verification = "Incomplete"
                        break

                if verification == "Incomplete":
                    break

                # put application in environment
                application = derivation_step.consequence

                new_assumptions = derivation_step.derivation.assumptions[::] + environment[::]

                new_assumptions = [
                    new_assumptions[i] for i in range(len(new_assumptions)) if
                    new_assumptions.index((new_assumptions[i])) == i
                ]

                derivation_step.derivation.assumptions = new_assumptions

                derivation_verification = derivation_step.derivation.verify(verify_number_at=i+1,
                                                                            join_after=False)

                valid_derivation = derivation_verification[-1] == "Q.E.D."

                if not valid_derivation:
                    print("Invalid subderivation", derivation_verification)
                    justification.append(["Invalid subderivation\n" + str(derivation_verification),
                                          'xx'])
                    self._final_i = i
                    verification = "Incomplete"
                    break

                sub_derivation = derivation_verification[1:-1]

                flag_i = str(i)

                for line in sub_derivation:
                    if type(line) is list:
                        find_assumptions = re.finditer(
                            r'asm(\d+)',
                            line[1]
                        )
                        replacements = []
                        for asm in find_assumptions:
                            match_name = asm.group(0)
                            match_num = int(asm.group(1))

                            from_assumptions = derivation_step.derivation.assumptions[match_num-1]
                            from_derives = self.derives.get(from_assumptions)

                            if from_derives is not None:
                                replacements.append(
                                    (match_name,
                                     str(from_derives))
                                )
                            else:
                                try:
                                    replacements.append(
                                        (match_name,
                                         f"asm{self.assumptions.index(from_assumptions) + 1}")
                                    )
                                except ValueError:
                                    pass

                        for old, new in replacements:
                            line[1] = line[1].replace(old, new)

                        justification.append([" ".join([
                            flag_i + " " * (len(str(len(self.derivation))) - len(flag_i) + 1),
                            line[0]]),
                            line[1]
                        ])

                    else:
                        justification.append([" ".join([
                            flag_i + " " * (len(str(len(self.derivation))) - len(flag_i) + 1),
                            line]),
                            ""
                        ])

                    flag_i = ""

                environment.append(application)
                self.derives.update({application: i})

                i = derivation_step.derivation.line_end_number
            else:
                derivation_step: Argument
                derivation_components = derivation_step.required_propositions()

                for dc in derivation_components:
                    try:
                        locations.append(str(self.derives[dc]))
                    except KeyError:
                        if dc in self.axioms:
                            locations.append(f"pr{self.axioms.index(dc)+1}")
                        elif dc in self.assumptions:
                            locations.append(f"asm{self.assumptions.index(dc) + 1}")

                for component in derivation_components:
                    if component not in environment:
                        print("Component not in environment", component)
                        justification.append(["Illegal Operation ?? " + str(component), 'xx'])
                        self._final_i = i
                        verification = "Incomplete"
                else:
                    try:
                        application = derivation_step.apply()
                    except LogicalException as log_exc:
                        if log_exc.logical_cause == "Contradiction":
                            environment.append(self.consequence)

                            justification.append([" ".join([
                                str(i) + " " * (len(str(len(self.derivation))) - len(str(i)) + 1),
                                TRUTH_SYMBOLS['f']]),
                                "id " + ", ".join(locations)
                            ])
                            break
                        else:
                            self._final_i = i
                            raise log_exc

                short_name = "".join([char.lower()
                                      for char in derivation_step.argument_name
                                      if char.isupper()])

                justification.append([" ".join([
                    str(i) + " " * (len(str(len(self.derivation))) - len(str(i)) + 1),
                    str(application),
                    ]),
                    short_name + " " + ", ".join(locations)
                ])

                environment.append(application)
                ##
                self.derives.update({application: i})

            prove_line = ""

            if application == self.consequence:
                prove_line = derivation_name_short

            if prove_line != "":
                # add line
                justification.append([str(i+1), prove_line + " " + str(self.derives[application])])

            i += 1

        if verification == "":
            if self.consequence in environment:
                verification += "Q.E.D."
            else:
                verification += "X < Incomplete / Incorrect > X"

        self._final_i = i

        ####

        axiom_and_consequence = " ".join([
            "; ".join([str(axiom) for axiom in sorted(list(set(self.axioms[::])),
                                                      key=lambda _: str(_))
                       if axiom not in set(self.assumptions[::])]),
            TRUTH_SYMBOLS['proves'], consequence_str])

        max_line_len = Derivation.max_line_len(justification)

        justification = Derivation.format_justification(max_line_len, justification, join_after)

        result = [
            axiom_and_consequence, f"Show {consequence_str}:", *justification, verification
        ]

        if join_after:
            return "\n".join(result)
        else:
            return result

    @classmethod
    def max_line_len(cls, justification):
        return max([max(
            [
                len(subline.rstrip()) for subline in str(line[0])
            ]
        ) for line in justification] + [20]) + 5

    @classmethod
    def format_justification(cls, max_line_len, justification, join_after):
        if join_after:
            return [
                "| " + line[0].rstrip() + " " * (max_line_len - len(line[0].rstrip()))
                + line[1].strip() for line in justification
            ]
        else:
            return [
                ["| " + line[0].rstrip(), line[1].strip()]
                for line in justification
            ]


class DirectDerivation(Derivation):
    """ [axioms]. ⊢ X
        -----------------
        Show X
        .
        .
        .
        Prove X / show contradiction in axioms.
     """
    def __init__(self,
                 axioms: list[Evaluable],
                 consequence: Evaluable,
                 derivation: list[Union[Argument, Derivation, SubDerivation]]):
        super().__init__("Direct Derivation", axioms, [], consequence, derivation)

    def verify(self, verify_number_at=1, join_after=True, con=None):
        return super().verify(verify_number_at, join_after=join_after,
                              consequence_str=str(self.consequence))


class ConditionalDerivation(Derivation):
    """ [axioms]. ⊢ X → Y
        -----------------
        Show X → Y
        Assume X
        .
        .
        .
        Prove Y / show contradiction.
     """
    def __init__(self,
                 axioms: list[Evaluable],
                 consequence: Evaluable,
                 derivation: list[Union[Argument, Derivation, SubDerivation]]):
        # need to add X as axiom
        assumptions = []
        self.old_consequence = consequence

        assert type(consequence) is LOGICAL_CONNECTIVES['implies']

        consequences: LogicalConnective
        assumptions.append(consequence.components[0])
        new_consequence = consequence.components[1]
        self.assumptions_str = str(consequence.components[0])

        derivation: list  # quiets warning on next line on -------vvv
        derivation = [Assumption(consequence.components[0])] + derivation

        super().__init__("Conditional Derivation", axioms,
                         assumptions, new_consequence, derivation)

    def __str__(self):
        string_repr = super().__str__()
        
        return " ".join([string_repr.split(TRUTH_SYMBOLS['proves'])[0].strip(),
                         TRUTH_SYMBOLS['proves'], str(self.old_consequence)])
            
    def __repr__(self):
        return self.__str__()

    def verify(self, verify_number_at=1, join_after=True, con=None):
        return super().verify(verify_number_at, join_after=join_after,
                              consequence_str=str(self.old_consequence))


class IndirectDerivation(Derivation):
    """ [axioms]. ⊢ Y
        -----------------
        Show Y
        Assume ¬Y
        .
        .
        .
        Leads to contradiction.
     """
    def __init__(self,
                 axioms: list[Evaluable],
                 consequence: Evaluable,
                 derivation: list[Union[Argument, Derivation, SubDerivation]]):

        # need to add X as axiom
        assumptions = [~consequence]
        self.assumptions_str = str(assumptions[0])

        derivation: list  # quiets warning here -----vvv
        derivation = [Assumption(~consequence)] + derivation

        super().__init__("Indirect Derivation", axioms,
                         [], consequence, derivation)

    def verify(self, verify_number_at=1, join_after=True, con=None):
        return super().verify(verify_number_at, join_after=join_after,
                              consequence_str=str(self.consequence))


class SubDerivation:
    def __init__(self,
                 derivation: Derivation,
                 environment: list[Evaluable] = None,
                 consequence: Evaluable = None,
                 parent: Union[Derivation, SubDerivation] = None
                 ):
        if environment is None:
            environment = []
        if parent is not None:
            self.parent = parent
            if issubclass(type(parent), Derivation):
                self.environment = environment + parent.assumptions[::] + parent.axioms[::]
            else:
                self.environment = environment + parent.environment[::]
        else:
            self.parent = None
            self.environment = None if environment == [] else environment
        self.derivation = derivation

        self.consequence = consequence
        if self.consequence is None and derivation is not None:
            if type(self.derivation) is ConditionalDerivation:
                self.derivation: ConditionalDerivation
                self.consequence = self.derivation.old_consequence
            else:
                self.consequence = self.derivation.consequence


if __name__ == '__main__':
    A, B, C = Atom.generate_atomics_set(3)

    print(ConditionalDerivation(
        axioms=[(A & B) >> C],
        consequence=A >> (B >> C),
        derivation=[
            ConditionalDerivation(
                axioms=[],
                consequence=B >> C,
                derivation=[
                    Conjunction(A, B),
                    ModusPonens((A & B) >> C, A & B)
                ]
            )
        ]
    ).verify())
