from __future__ import annotations
from sortedcontainers import SortedDict
from Propositional.arguments import *
import traceback
import sys
import re


class Derivation:
    def __init__(self,
                 derivation_kind: str,
                 axioms: list[Evaluable],
                 assumptions: list[Evaluable],
                 consequence: Evaluable,
                 derivation: list[Union[Argument, Subderivation]]):
        self.derivation_kind = derivation_kind
        self.axioms = axioms
        self.assumptions = assumptions
        self.consequence = consequence
        self.derivation = derivation

    def is_valid(self):
        return self.get_counter_example() is None

    def __str__(self):
        axioms = "; ".join([
            str(axiom) for axiom in self.axioms
        ] + [
            "["+str(assumption)+"]" for assumption in self.assumptions
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
                    str(atom) if tv else str(LogicalNot(atom)) for atom, tv in atom_ordered.items()
                ])
                counter_example = f"({counter_example})"

                return counter_example

        return None

    def verify(self):
        counter = self.get_counter_example()
        if counter is not None and type(self) != IndirectDerivation:
            print(type(self))

            print(self.axioms)

            print([str(x) for x in self.assumptions])

            print(self.consequence)
            print(f"Found counter example {counter}")
            return None, None

        justification = []

        derivation_name_short = "".join([
            char.lower() for char in self.derivation_kind if char.isupper()
        ])

        environment = self.axioms[::] + self.assumptions[::]
        derives = {}
        i = 1

        if not self.derivation:
            self.derivation = [
                Repeat(self.consequence)
            ]

        for derivation_step in self.derivation:
            locations = []

            if type(derivation_step) is Subderivation:
                # needs to find applicable form. for now, only literal.
                for e in derivation_step.environment:
                    if e not in environment:
                        # illegal (needs tweaks)
                        print("Component not in environment", e)
                        justification.append("Illegal Operation ?? " + str(e))
                        return justification, "Incomplete"

                # put application in environment
                application = derivation_step.consequence

                new_assumptions = derivation_step.derivation.assumptions[::] + environment[::]

                new_assumptions = [
                    new_assumptions[i] for i in range(len(new_assumptions)) if
                    new_assumptions.index((new_assumptions[i])) == i
                ]

                derivation_step.derivation.assumptions = new_assumptions

                derivation_verification = derivation_step.derivation.verify()

                valid_derivation = derivation_verification.endswith("Q.E.D.")
                if not valid_derivation:
                    print("Invalid subderivation", derivation_verification)
                    justification.append("Invalid subderivation\n" + derivation_verification)
                    return justification, "Incomplete"

                derivation_verification = "\n".join(derivation_verification.split("\n")[1:-1])

                sub_derivation = derivation_verification.split("\n")

                flag_i = str(i)

                for line in sub_derivation:
                    m = re.search(
                        r'(((\w{1,4}) (((pr|asm)?\d+), )*((pr|asm)?\d+)))|((dd|cd|id).+)',
                    line)

                    add_extra = False

                    if m is not None:
                        last_bit = m.groups()[0].strip()

                        if line.strip().endswith(last_bit):
                            line, loc = line[:-len(last_bit)].rstrip(), last_bit

                            justification.append([" ".join([
                                flag_i + " " * (len(str(len(self.derivation))) - len(flag_i) + 1),
                                line]),
                                loc
                            ])

                        else:
                            add_extra = True
                    else:
                        add_extra = True

                    if add_extra:
                        justification.append([" ".join([
                            flag_i + " " * (len(str(len(self.derivation))) - len(flag_i) + 1),
                            line]),
                            ""
                        ])
                    flag_i = ""

                environment.append(application)
                derives.update({application: i})

            else:
                derivation_step: Argument

                derivation_components = derivation_step.required_propositions()

                for dc in derivation_components:
                    if dc in self.axioms:
                        locations.append(f"pr{self.axioms.index(dc)+1}")
                    elif dc in self.assumptions:
                        locations.append(f"asm{self.assumptions.index(dc) + 1}")
                    else:
                        try:
                            locations.append(str(derives[dc]))
                        except KeyError:
                            pass

                for component in derivation_components:
                    if component not in environment:
                        print("Component not in environment", component)
                        justification.append("Illegal Operation ?? " + str(component))
                        return justification, "Incomplete"
                else:
                    try:
                        application = derivation_step.apply()
                    except LogicalException as log_exc:
                        if log_exc.logical_cause == "Contradiction":
                            environment.append(self.consequence)

                            justification.append([" ".join([
                                str(i) + " " * (len(str(len(self.derivation))) - len(str(i)) + 1),
                                str(derivation_step.l1),
                                LOGICAL_SYMBOLS["and"],
                                str(derivation_step.l2) ]),
                                "id " + ", ".join(locations)
                            ])
                            break
                        else:
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

            prove_line = ""

            if application == self.consequence:
                prove_line = derivation_name_short

            if prove_line != "":
                # add line
                justification.append([str(i+1), prove_line + " " + str(i)])

            environment.append(application)
            derives.update({application: i})

            i += 1

        verification = ""
        if self.consequence in environment:
            verification += "Q.E.D."
        else:
            verification += "X < Incomplete / Incorrect > X"

        return justification, verification


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
                 derivation: list[Union[Argument, Subderivation]]):
        super().__init__("Direct Derivation", axioms, [], consequence, derivation)

    def verify(self):
        try:
            justification, verification = super().verify()
        except TypeError:
            return None

        consequence = str(self.consequence)

        axiom_and_consequence = " ".join(["; ".join([str(axiom)
                                                     for axiom in sorted(list(set(self.axioms)),
                                                                         key=lambda x: x.name)]),
                                          TRUTH_SYMBOLS['proves'],
                                          str(self.consequence)])

        max_line_len = max([
                               max([len(subline) for subline in str(line[0]).split("\n")])
                               for line in justification
                           ] + [20])

        justification = [
            " | " + line[0] + " " * (max_line_len - len(line[0]) + 2) + line[1]
            if not line[0].startswith("Illegal") else line
            for line in justification
        ]

        return "\n".join([
            axiom_and_consequence, f"Show {consequence}:", *justification, verification
        ])


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
                 derivation: list[Argument]):

        # need to add X as axiom
        assumptions = []
        self.old_consequence = consequence

        assert type(consequence) is LogicalImplies
        consequences: LogicalConnective
        assumptions.append(consequence.components[0])
        new_consequence = consequence.components[1]

        super().__init__("Conditional Derivation", axioms,
                         assumptions, new_consequence, derivation)

    def __str__(self):
        string_repr = super().__str__()
        
        return " ".join([string_repr.split(TRUTH_SYMBOLS['proves'])[0].strip(), TRUTH_SYMBOLS['proves'], str(self.old_consequence)])
            
    def __repr__(self):
        return self.__str__()

    def verify(self):
        try:
            justification, verification = super().verify()
        except TypeError:
            return None

        axiom_and_consequence = " ".join(["; ".join([str(axiom)
                                                     for axiom in sorted(list(set(self.axioms)),
                                                                         key=lambda x: x.name)
                                                     if axiom not in set(self.assumptions)]),
                                          TRUTH_SYMBOLS['proves'],
                                          str(self.old_consequence)])

        consequence = str(self.old_consequence)

        assumptions_str = ", ".join([str(assumption) for assumption in self.assumptions])

        max_line_len = max([
                               max([len(subline) for subline in str(line[0]).split("\n")])
                               for line in justification
                           ] + [20])

        justification = [
            " | " + line[0] + " " * (max_line_len - len(line[0]) + 2) + line[1]
            if not line[0].startswith("Illegal") else line
            for line in justification
        ]

        return "\n".join([
            axiom_and_consequence, f"Show {consequence}:", f"Assume {assumptions_str}",
            *justification, verification
        ])


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
                 derivation: list[Union[Argument, Subderivation]]):

        # need to add X as axiom
        assumptions = [LogicalNot(consequence)]

        super().__init__("Indirect Derivation", axioms,
                         assumptions, consequence, derivation)

    def verify(self):
        try:
            justification, verification = super().verify()
        except TypeError as e:
            print("Type Error", e)
            traceback.print_exception(*sys.exc_info())
            return None

        axiom_and_consequence = " ".join(["; ".join([str(axiom)
                                                     for axiom in sorted(list(set(self.axioms)),
                                                                         key=lambda x: x.name)
                                                     if axiom not in set(self.assumptions)]),
                                          TRUTH_SYMBOLS['proves'],
                                          str(self.consequence)])

        consequence = str(self.consequence)

        assumptions_str = ", ".join([str(assumption) for assumption in self.assumptions])

        max_line_len = max([
                               max([len(subline) for subline in str(line[0]).split("\n")])
                               for line in justification
                           ] + [20])

        justification = [
            " | " + line[0] + " " * (max_line_len - len(line[0]) + 2) + line[1]
            if not line[0].startswith("Illegal") else line
            for line in justification
        ]

        return "\n".join([
            axiom_and_consequence, f"Show {consequence}:", f"Assume {assumptions_str}",
            *justification, verification
        ])


class Subderivation:
    """

    """
    def __init__(self,
                 parent: Union[Derivation, Subderivation],
                 environment: list[Evaluable],
                 consequence: Evaluable,
                 derivation: Derivation):
        self.parent = parent
        if issubclass(type(parent), Derivation):
            self.environment = environment + parent.assumptions[::] + parent.axioms[::]
        else:
            self.environment = environment + parent.environment[::]
        self.consequence = consequence
        self.derivation = derivation


if __name__ == '__main__':
    PL = parse_logical

    axiomsDM = [
        PL("A or B")
    ]

    consequencesDM = PL("not ((not A) and (not B))")

    derivationDM = [
        DoubleNegation(PL("not (not ((not A) and (not B)))"), PL("(not A) and (not B)")),
        Simplification(PL("(not A) and (not B)"), PL("not A")),
        Simplification(PL("(not A) and (not B)"), PL("not B")),
        ModusTollendoPonens(PL("A or B"), PL("not A")),
        Contradiction(PL("B"), PL("not B"))
    ]

    pDM = IndirectDerivation(
        axiomsDM,
        consequencesDM,
        derivationDM
    )

    print(pDM.verify())
    print("---------")

    axioms1 = [
        PL("A"), PL("not A")
    ]

    consequences1 = PL("B")

    derivation1 = [
        Contradiction(PL("A"), PL("not A"))
    ]

    p1 = DirectDerivation(
        axioms1,
        consequences1,
        derivation1
    )

    print(p1.verify())
    print("---------")
