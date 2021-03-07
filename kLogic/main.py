from Propositional.logical import Atom
from Propositional.derivations import DirectDerivation, ConditionalDerivation, IndirectDerivation
from Propositional.arguments import Addition, ModusPonens, ModusTollens, ModusTollendoPonens, Conjunction, Contradiction
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
    print("-" * 25)

    # Turn into a theorem.
    constructive_dilemma = Theorem('Constructive Dilemma', dd)

    # use the theorem in another derivation.
    dd2 = IndirectDerivation(
        axioms=[A >> B, (~A) >> C],
        consequence=B | C,
        derivation=[
            TertiumNonDatur(therefore=A | (~A)),
            constructive_dilemma(A | (~A), A >> B, (~A) >> C, therefore=B | C)
        ]
    )

    print(dd2.verify())
    print("-" * 25)

    # separate question. Good example

    P, Q, R = [Atom(chr(ord("P") + i)) for i in range(3)]

    print(IndirectDerivation(
        axioms=[(~P) | (~Q), (~P) >> Q, (P & ~Q) >> R, (~P & Q) >> R],
        consequence=R,
        derivation=[
            ModusTollens((P & ~Q) >> R, ~R),
            ModusTollens((~P & Q) >> R, ~R),
            ConditionalDerivation(
                axioms=[],
                consequence=P >> Q,
                derivation=[
                    IndirectDerivation(
                        axioms=[],
                        consequence=Q,
                        derivation=[
                            Conjunction(P, ~Q),
                            Contradiction(P & ~Q, ~(P & ~Q))
                        ]
                    )
                ]
            ),
            ConditionalDerivation(
                axioms=[],
                consequence=Q >> P,
                derivation=[
                    IndirectDerivation(
                        axioms=[],
                        consequence=P,
                        derivation=[
                            Conjunction(~P, Q),
                            Contradiction(~P & Q, ~(~P & Q))
                        ]
                    )
                ]
            ),
            TertiumNonDatur(therefore=P | ~P),
            DisjunctionElimination(P | ~P, P >> Q, ~P >> Q, therefore=Q),
            ModusTollendoPonens(Q, ~P | ~Q),
            Conjunction(~P, Q),
            ModusPonens(~P & Q, (~P & Q) >> R)
        ]
    ).verify())
