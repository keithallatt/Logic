#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Unit tests for klogic module.

@author: Keith Allatt
@version: 1.1
"""

import unittest
import random
from klogic.Propositional import *


def generate_test_cases(num_vars: int = 4, num_examples=30, prop_depth=5):
    """ Generate a set of test cases """
    atomics = logical.Atom.generate_atomics_set(num_vars)
    tests = {}

    def _generate_example(depth):
        """
        Generate exactly one example for a test case.

        :param depth: The depth of the proposition (the highest number of nested propositions)
        :return: One (1) test case.
        """
        if depth <= 0:
            atom = atomics[random.randrange(0, len(atomics))]
            return atom.name, atom

        connective = random.choice(list(logical.LOGICAL_CONNECTIVES.keys()))

        if connective == "not":
            name_, prop_ = _generate_example(depth - 1)
            return f"(not {name_})", ~prop_

        depth1 = depth-1
        depth2 = random.randrange(0, depth)

        if random.random() < 0.5:
            depth1, depth2 = depth2, depth1

        name1, prop1 = _generate_example(depth1)
        name2, prop2 = _generate_example(depth2)

        return f"({name1} {connective} {name2})", \
               logical.LOGICAL_CONNECTIVES[connective](prop1, prop2)

    for i in range(num_examples):
        name, prop = _generate_example(depth=prop_depth)
        while name in tests:
            name, prop = _generate_example(depth=prop_depth)
        tests.update({name: prop})

    return tests


class TestLogical0thOrder(unittest.TestCase):
    """ Test Propositional.logical.py """
    def test_pl(self):
        """ Test propositional logic parsing. """
        tests = generate_test_cases(num_vars=10, num_examples=100, prop_depth=3)

        for actual, expected in tests.items():
            with self.subTest(expected=expected, actual=actual):
                # test parse logical
                self.assertEqual(
                    logical.parse_logical(actual), expected,
                    msg=f"Expected '{expected}', got '{logical.parse_logical(actual)}'")
                # test PL-ify (return to text representation)
                self.assertEqual(
                    logical.parse_logical(expected.pl_ify()), expected,
                    msg=f"Expected '{expected}', got '{logical.parse_logical(expected.pl_ify())}'")

    def test_invalid_pl(self):
        """ Test propositional logic parsing, specifically non-examples. """
        invalid_examples = [
            "A and B or C",  # ambiguous structure for binary relations.
            "((A implies B)",  # mismatched parentheses (too many open)
            "(B implies C))",  # mismatched parentheses (too many close)
            "C xor D",  # invalid keyword
        ]

        for example in invalid_examples:
            with self.subTest(example=example):
                try:
                    self.fail(f"Parse logical produced {logical.parse_logical(example)} when it "
                              f"should've produced an error.")
                except logical.LogicalException:
                    pass

    def test_reflexivity_of_equivalence(self):
        """ Test if propositions are always equivalent to themselves.
            (Reflexive property) """
        tests = list(generate_test_cases(num_vars=10, num_examples=100, prop_depth=7).values())

        for test_case in tests:
            self.assertTrue(test_case.equiv(test_case), msg=f"Test case {test_case} was not"
                                                            f"considered equivalent to itself.")

    def test_symmetry_of_equivalence(self):
        """ Test if a proposition is equivalent to another, the other is equivalent to this.
            (Symmetric property) """
        tests = list(generate_test_cases(num_vars=7, num_examples=50, prop_depth=3).values())
        tests: list[logical.Evaluable]

        for test_case1 in tests:
            for test_case2 in tests:
                if test_case1.equiv(test_case2):
                    self.assertTrue(
                        test_case2.equiv(test_case1),
                        msg=f"Test case {test_case1} was considered equivalent to {test_case2}, "
                            f"but {test_case2} was not considered equivalent to {test_case1}"
                    )

    def test_transitivity_of_equivalence(self):
        """ Test if proposition A is equivalent to proposition B, and proposition B is
            equivalent to proposition C, then proposition A is equivalent to proposition C.
            (Transitive property) """
        tests = list(generate_test_cases(num_vars=5, num_examples=35, prop_depth=3).values())

        for test_case1 in tests:
            for test_case2 in tests:
                for test_case3 in tests:
                    if test_case1.equiv(test_case2) and test_case2.equiv(test_case3):
                        self.assertTrue(
                            test_case1.equiv(test_case3),
                            msg=f"Test case {test_case1} equiv. to {test_case2}, and "
                                f"{test_case2} equiv. to {test_case3} but {test_case1}"
                                f" was not equivalent to {test_case3}."
                        )


class TestTheorems0thOrder(unittest.TestCase):
    """ Test Propositional.theorem.py """
    def test_theorems(self):
        for thing in vars(theorem):
            obj = vars(theorem)[thing]
            if type(obj) == theorem.Theorem:
                self.assertTrue(obj.argument.argument_complete(),
                                msg=f"Theorem : {obj} is incomplete.")


if __name__ == '__main__':
    unittest.main(verbosity=2)
