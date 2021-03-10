#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""

@author: Keith Allatt
@version: 1.1
"""


from klogic.Propositional.derivations import *

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
