from Propositional.logical import Atom
from Propositional.derivations import DirectDerivation, ConditionalDerivation, IndirectDerivation
from Propositional.arguments import Addition, ModusPonens, ModusTollens, ModusTollendoPonens
from Propositional.theorem import DisjunctionElimination, TertiumNonDatur, Theorem

if __name__ == '__main__':
    """
        Proof of Constructive Dilemma:
        If A or B; A implies C; B implies D; therefore B or D.
    """
    A, B, C, D = Atom.generate_atomics_set(4)
    dd = DirectDerivation(
        axioms=[A | B, A >> C, B >> D],
        consequence=C | D,
        derivation=[
            ConditionalDerivation(
                axioms=[],
                consequence=C >> (C | D),
                derivation=[
                    Addition(C, C | D)
                ]
            ),
            ConditionalDerivation(
                axioms=[],
                consequence=(~C) >> (C | D),
                derivation=[
                    ModusTollens(~C, A >> C),
                    ModusTollendoPonens(~A, A | B),
                    ModusPonens(B, B >> D),
                    Addition(D, C | D)
                ]
            ),
            TertiumNonDatur(therefore=C | (~C)),
            DisjunctionElimination(C >> (C | D), (~C) >> (C | D), C | (~C), therefore=C | D)
        ]
    )

    print(dd.verify())

    # Turn into a theorem.
    constructive_dilemma = Theorem('Constructive Dilemma', dd)

    dd2 = IndirectDerivation(
        axioms=[A >> B, (~A) >> C],
        consequence=B | C,
        derivation=[
            TertiumNonDatur(therefore=A | (~A)),
            constructive_dilemma(A | (~A), A >> B, (~A) >> C, therefore=B | C)
        ]
    )

    print(dd2.verify())
