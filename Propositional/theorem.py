from Propositional.derivations import *


class Theorem(Argument):
    """
    Essentially the same as a Subderivation, but in general form. Therefore we can define objects
    that can allow us to use 'call into existence' a version of the proof where each atomic
    proposition in the theorem can be replaced with a valid formula and achieve propositions
    in the environment of the derivation.

    """

    def __init__(self, argument_name: str, argument: Derivation):
        super().__init__(argument_name)
        self.argument = argument
        self.therefore = None
        self._instance = False

    def get_application(self) -> Union[Evaluable, None]:
        if len(self.ls) != len(self.argument.axioms):
            return None

        if not self._instance:
            raise LogicalException("Can't get application of uncalled instance.")

        if "Q.E.D." not in self.argument.verify():
            print("Basic argument not valid:")
            print(self.argument.verify())
            return None

        if len(self.argument.axioms) == 0:
            # tautology member.
            if forms := self.therefore.search(self.argument.consequence):
                return self.argument.consequence.replace(forms)
            return None

        def permutations(lst: list):
            if len(lst) <= 1:
                yield lst
            for i in range(len(lst)):
                item = lst[i]
                sub_lst = lst[:i] + lst[i + 1:]
                for sub_perm in permutations(sub_lst):
                    yield [item] + sub_perm

        for perm in permutations(list(self.ls)):
            forms = []

            for ax, l in zip(self.argument.axioms, perm):
                perm_works = True
                for form_i, value_i in l.search(ax):
                    for form_contained, value_contained in forms:
                        if form_i == form_contained:
                            if value_i == value_contained:
                                break
                            perm_works = False
                    else:
                        forms.append((form_i, value_i))

                if not perm_works:
                    continue

            if set([axiom.replace(forms) for axiom in self.argument.axioms]) == set(self.ls):
                therefore = self.argument.consequence.replace(forms)
                return therefore

        return None

    def required_propositions(self):
        return self.ls

    def argument_complete(self):
        return self.argument.argument_complete()

    def __call__(self, *args, **kwargs):
        therefore = kwargs.get('therefore', None)
        ls = args
        clone_obj = Theorem(self.argument_name, self.argument)
        clone_obj.ls = ls
        clone_obj.therefore = therefore
        clone_obj._instance = True

        return clone_obj

    def verify(self):
        return self.argument.verify()

    def __str__(self):
        if self._instance:
            return super().__str__()
        else:
            return f"{self.argument_name}: {self.argument}"

    def __repr__(self):
        return self.__str__()


PL = parse_logical

# SETUP #

DisjunctionElimination = Theorem("Disjunction Elimination", IndirectDerivation(
    axioms=[
        PL("A or B"), PL("A implies C"), PL("B implies C")
    ],
    consequence=PL("C"),
    derivation=[
        ModusTollens(PL("A implies C"), PL("not C")),
        ModusTollens(PL("B implies C"), PL("not C")),
        ModusTollendoPonens(PL("not B"), PL("A or B")),
        Contradiction(PL("A"), PL("not A"))
    ]
))

TertiumNonDatur = Theorem("Tertium Non Datur", IndirectDerivation(
    axioms=[],
    consequence=PL("A or (not A)"),
    derivation=[
        ConditionalDerivation(
            axioms=[],
            consequence=PL("A implies (A or (not A))"),
            derivation=[
                Addition(PL("A"), PL("A or (not A)"))
            ]),
        ConditionalDerivation(
            axioms=[],
            consequence=PL("(not A) implies (A or (not A))"),
            derivation=[
                Addition(PL("not A"), PL("A or (not A)"))
            ]),
        ModusTollens(PL("not (A or (not A))"), PL("A implies (A or (not A))")),
        ModusTollens(PL("not (A or (not A))"), PL("(not A) implies (A or (not A))")),
        Contradiction(PL("not A"), PL("not (not A)"))
    ]))

LawOfNonContradiction = Theorem("Law of Non-Contradiction", IndirectDerivation(
    axioms=[],
    consequence=PL("not (A and (not A))"),
    derivation=[
        DoubleNegation(~~PL("A and (not A)"), PL("A and (not A)")),
        Simplification(PL("A and (not A)"), PL("A")),
        Simplification(PL("A and (not A)"), PL("not A")),
        Contradiction(PL("A"), PL("not A"))
    ]
))

DeMorgansLaws1 = Theorem("De Morgans 1", IndirectDerivation(
    axioms=[PL("(not A) and (not B)")],
    consequence=PL("not (A or B)"),
    derivation=[
        DoubleNegation(~~PL("A or B"), PL("A or B")),
        Simplification(PL("(not A) and (not B)"), PL("not A")),
        Simplification(PL("(not A) and (not B)"), PL("not B")),
        ModusTollendoPonens(PL("A or B"), PL("not B")),
        Contradiction(PL("A"), PL("not A"))
    ]
))

DeMorgansLaws2 = Theorem("De Morgans 2", DirectDerivation(
    axioms=[PL("not (A or B)")],
    consequence=PL("(not A) and (not B)"),
    derivation=[
        IndirectDerivation(
            axioms=[],
            consequence=PL("not A"),
            derivation=[
                DoubleNegation(~~PL("A"), PL("A")),
                Addition(PL("A"), PL("A or B")),
                Contradiction(PL("A or B"), PL("not (A or B)"))
            ]
        ),
        IndirectDerivation(
            axioms=[],
            consequence=PL("not B"),
            derivation=[
                DoubleNegation(~~PL("B"), PL("B")),
                Addition(PL("B"), PL("A or B")),
                Contradiction(PL("A or B"), PL("not (A or B)"))
            ]
        ),
        Conjunction(PL("not A"), PL("not B"))
    ]
))


if __name__ == '__main__':
    for derived in [
        DisjunctionElimination,
        TertiumNonDatur,
        LawOfNonContradiction,
        DeMorgansLaws1,
        DeMorgansLaws2
    ]:
        print("-" * 25)
        print(derived.argument_name)

        print(derived.argument.verify())

