from derivations import *

if __name__ == '__main__':
    PL = parse_logical

    axioms = [

    ]

    consequences = PL("(A implies B) implies ((not A) or B)")

    derivation = []

    dd = ConditionalDerivation(
        axioms, consequences, derivation
    )

    ###

    consequence_sub_ind = PL("((not A) or B)")

    derivation_sub_ind = [

    ]

    cd_sub_ind = IndirectDerivation(
        axioms, consequence_sub_ind, derivation_sub_ind
    )

    sub_ind = Subderivation(dd, axioms, PL("((not A) or B)"), cd_sub_ind)

    ###

    consequence_sub1 = PL("A implies ((not A) or B)")

    derivation_sub1 = [
        ModusPonens(PL("A implies B"), PL("A")),
        Addition(PL("B"), PL("((not A) or B)"))
    ]

    cd_sub1 = ConditionalDerivation(
        axioms, consequence_sub1, derivation_sub1
    )

    sub1 = Subderivation(sub_ind, axioms, consequence_sub1, cd_sub1)

    ###

    consequence_sub2 = PL("(not A) implies ((not A) or B)")

    derivation_sub2 = [
        Addition(PL("not A"), PL("((not A) or B)"))
    ]

    cd_sub2 = ConditionalDerivation(
        axioms, consequence_sub2, derivation_sub2
    )

    sub2 = Subderivation(sub_ind, axioms, consequence_sub2, cd_sub2)

    derivation_sub_ind = [
        sub1,
        sub2,
        ModusTollens(PL("not ((not A) or B)"), PL("A implies ((not A) or B)")),
        ModusTollens(PL("not ((not A) or B)"), PL("(not A) implies ((not A) or B)")),
        Contradiction(PL("not A"), PL("not (not A)"))
    ]

    sub_ind.derivation.derivation = derivation_sub_ind

    derivation = [
        sub_ind
    ]

    dd.derivation = derivation

    print(dd.verify())
