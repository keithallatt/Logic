#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Propositional logic module. Contains basic atomic propositions

@author: Keith Allatt
@version: 1.11
"""

from __future__ import annotations
from abc import abstractmethod
from typing import Union, Callable
from klogic import symbolic
import copy

# Unicode logical symbols (propositional logic)
LOGICAL_SYMBOLS = symbolic.LogicalSymbolSet()
TRUTH_SYMBOLS = symbolic.TruthSymbolSet()


class LogicalException(Exception):
    """ Exception relating to logical mistakes. """
    def __init__(self, cause=None):
        super().__init__(cause)
        self.logical_cause = cause


# enforce that logical connectives must be binary, unless exempt.
# if this is false, then any connective can have any number of parameters.
# If this is ever false, then some behaviour
ENFORCE_BINARY_OPERATIONS = True


class Evaluable:
    """ A boolean evaluable expression. """
    def __init__(self, name):
        self.name = name

    @abstractmethod
    def __bool__(self):
        """
        Return the boolean evaluation of this evaluable object.

        :return: the truth value of 'self'
        """
        pass

    def __and__(self, other):
        """
        Returns a logical 'and' connective between these elements.

        :param other: another evaluable to connect to.
        :return: 'self' and 'other'
        """
        return LOGICAL_CONNECTIVES['and'](self, other)
    
    def __rand__(self, other):
        """
        Returns a logical 'and' connective between these elements.

        :param other: another evaluable to connect to.
        :return: 'self' and 'other'
        """
        return self.__and__(other)
    
    def __or__(self, other):
        """
        Returns a logical 'or' connective between these elements.

        :param other: another evaluable to connect to.
        :return: 'self' or 'other'
        """
        return LOGICAL_CONNECTIVES['or'](self, other)
    
    def __ror__(self, other):
        """
        Returns a logical 'or' connective between these elements.

        :param other: another evaluable to connect to.
        :return: 'self' or 'other'
        """
        return self.__or__(other)
    
    def __invert__(self):
        """
        Returns a logical 'not' connective between these elements.

        :return: not 'self'
        """
        return LOGICAL_CONNECTIVES['not'](self)

    def __rshift__(self, other):
        """
        Returns a logical 'implies' connective between these elements.

        :param other: another evaluable to connect to.
        :return: 'self' implies 'other'
        """
        return LOGICAL_CONNECTIVES['implies'](self, other)

    def __lshift__(self, other):
        """
        Returns a logical 'implies' connective between these elements.

        :param other: another evaluable to connect to.
        :return: 'self' is implied by 'other'
        """
        return LOGICAL_CONNECTIVES['implies'](other, self)

    def __xor__(self, other):
        """
        Returns a logical 'iff' connective between these elements.

        (XOR bitwise operator was the last available. Technically xor is the
        negation of iff, (which is equivalent to not (A xor B), or A x-nor B).

        :param other: another evaluable to connect to.
        :return: 'self' if and only if 'other'
        """
        return LOGICAL_CONNECTIVES['iff'](self, other)

    def atoms_contained(self):
        """
        Get the atomic propositions contained in this evaluable.

        :return: A list of contained atomic propositions.
        """
        return []  # no atoms contained in a generic evaluable.

    def truth_table(self, atomics, regen=False):
        """
        Generate the truth table for this example with respect to these atomics.

        :param atomics: A list to generate the truth table with respect to.
        :param regen: Regenerate the truth table even if the atomics are the same.
        :return: A list of truth table rows, each row consisting of a tuple, the first
                 component being a list of atomic proposition names and their truth
                 values, the second component being the truth value of the evaluable.
        """
        raise NotImplementedError("Cannot get truth table for generic evaluable.")

    def truth_hash(self, atomics, regen=False):
        """
        Generate a hash corresponding to the truth table for
        this example with respect to these atomics.

        :param atomics: A list to generate the truth hash with respect to.
        :param regen: Regenerate the truth hash even if the atomics are the same.
        :return: an integer 'n' such that 0 <= n < 2^(number of atoms), corresponding
                 to a binary number found by reading the truth value rows, rows with
                 True corresponding to the binary digit 1 and False corresponding to 0.
                 MSD of the hash corresponds to the truth value of the propositions
                 when all propositions are true, and LSD of the hash corresponds to
                 the truth value of the proposition
        """
        raise NotImplementedError("Cannot get truth table hash for generic evaluable.")

    def equiv(self, other: Evaluable, regen=False):
        """
        Return if two evaluables are equivalent, by checking the truth table generated


        :param other:
        :param regen:
        :return:
        """
        self_atoms = set(self.atoms_contained())
        other_atoms = set(other.atoms_contained())
        atomics = list(self_atoms.union(other_atoms))

        self_truth = self.truth_table(atomics, regen)
        other_truth = other.truth_table(atomics, regen)

        self_str = {
            str(_) for _ in self_truth
        }
        other_str = {
            str(_) for _ in other_truth
        }

        return self_str.symmetric_difference(other_str) == set()

    def __hash__(self):
        return hash(self.__str__())

    def copy(self):
        """ Copy an evaluable. If this is being used, just use the base deep copy. """
        return copy.deepcopy(self)

    def set_atom_truth_values(self, context):
        raise NotImplementedError("Cannot set atomic truth values to generic evaluable.")

    def pl_ify(self):
        raise NotImplementedError("Cannot PL-ify to generic evaluable.")

    def replace(self, forms):
        raise NotImplementedError("Cannot replace in generic evaluable.")


class Tautology(Evaluable):
    def __bool__(self):
        return True

    def __str__(self):
        return str(TRUTH_SYMBOLS['tautology'])

    def __repr__(self):
        return self.__str__()

    def atoms_contained(self):
        return []

    def truth_table(self, atomics, regen=False):
        truth_table = []
        for i in range(2 ** len(atomics)):
            context = {atomics[a]: (i & 1 << a) != 0 for a in range(len(atomics))}

            lst = []
            names = []
            for k in sorted(list(context.keys())):
                if k.name not in names:
                    lst.append((Atom(k.name), context[k]))
                    names.append(k.name)

            truth_table.append(
                (lst, bool(self))
            )
        return truth_table

    def truth_hash(self, atomics, regen=False):
        return 2 ** len(atomics) - 1

    def set_atom_truth_values(self, context):
        pass

    def pl_ify(self):
        raise NotImplementedError("Cannot PL-ify Tautologies.")

    def replace(self, forms):
        raise NotImplementedError("Cannot replace in Tautologies.")


class Falsehood(Evaluable):
    def __bool__(self):
        return False

    def __str__(self):
        return str(TRUTH_SYMBOLS['falsehood'])

    def __repr__(self):
        return self.__str__()

    def atoms_contained(self):
        return []

    def truth_table(self, atomics, regen=False):
        truth_table = []
        for i in range(2 ** len(atomics)):
            context = {atomics[a]: (i & 1 << a) != 0 for a in range(len(atomics))}

            lst = []
            names = []
            for k in sorted(list(context.keys())):
                if k.name not in names:
                    lst.append((Atom(k.name), context[k]))
                    names.append(k.name)

            truth_table.append(
                (lst, bool(self))
            )
        return truth_table

    def truth_hash(self, atomics, regen=False):
        return 0

    def set_atom_truth_values(self, context):
        pass

    def pl_ify(self):
        raise NotImplementedError("Cannot PL-ify Falsehood.")

    def replace(self, forms):
        raise NotImplementedError("Cannot replace in Falsehood.")


class Atom(Evaluable):
    """ Logical Atom. Represents a variable / truth value.
        This is the smallest unit in 0th order logic. """
    def __init__(self, name: str, truth_value: bool = None):
        super(Atom, self).__init__(name)
        self.truth_value = truth_value
        self.truth_table_cached = None
        self.truth_hash_cached = None

    def __bool__(self):
        if self.truth_value is None:
            return False
        return self.truth_value

    def replace(self, old: Union[list[tuple[Evaluable, Evaluable]], Evaluable] = None,
                new: Evaluable = None, lst: list[tuple[Evaluable, Evaluable]] = None):
        if type(old) is list:
            if lst is None:
                lst = old[::]
            else:
                lst += old[::]
            old = None
        if lst is None and (old is None or new is None):
            return self.copy()
        if lst is not None and old is not None and new is not None:
            if type(old) is Evaluable:
                lst.append((old, new))
        if lst is None:
            lst = [(old, new)]

        for old_l, new_l in lst:
            if self == old_l:
                return new_l.copy()

        return self.copy()

    def copy(self):
        new_atom = Atom(self.name, self.truth_value)
        new_atom.truth_table_cached = copy.deepcopy(self.truth_table_cached)
        new_atom.truth_hash_cached = copy.deepcopy(self.truth_hash_cached)
        return new_atom

    def search(self, form: Evaluable):
        if type(form) is Atom:
            form: Atom
            return [(form.copy(), self.copy())]
        return []

    def atoms_contained(self):
        return [self]

    def set_atom_truth_values(self, context):
        for c in context.keys():
            if c.name == self.name:
                self.truth_value = context[c]
                break
        else:
            raise LogicalException("Missing key:" + str(self))

    def truth_table(self, atomics, regen=False):
        if self.truth_table_cached is None or regen:
            truth_table = []
            for i in range(2 ** len(atomics)):
                context = {atomics[a]: (i & 1 << a) != 0 for a in range(len(atomics))}
                self.set_atom_truth_values(context)

                lst = []
                names = []
                for k in sorted(list(context.keys())):
                    if k.name not in names:
                        lst.append((Atom(k.name), context[k]))
                        names.append(k.name)

                truth_table.append(
                    (lst, bool(self))
                )

            self.truth_table_cached = truth_table
        return self.truth_table_cached

    def truth_hash(self, atomics, regen=False):
        if self.truth_hash_cached is None or regen:
            truth = self.truth_table(atomics, regen)

            truth = [
                (sorted(elem[0], key=lambda x: x[0]), elem[1]) for elem in truth
            ]

            truth = [
                (sum([
                    (1 << i if elem[0][i][1] else 0) for i in range(len(atomics))
                ]), elem[1]) for elem in truth
            ]

            truth = sorted(truth, key=lambda x: x[0])

            t_hash = ([
                (1 << i if truth[i][1] else 0) for i in range(len(truth))
            ])

            self.truth_hash_cached = sum(t_hash)
        return self.truth_hash_cached

    def __eq__(self, other):
        return type(other) == Atom and \
               self.name == other.name and \
               (self.truth_value == other.truth_value or
                self.truth_value is None or
                other.truth_value is None)

    def __str__(self):
        return str(self.name)
    
    def __repr__(self):
        return str(self)

    def __lt__(self, other):
        if type(other) is Atom:
            return self.name < other.name
        else:
            return False

    def __hash__(self):
        return hash(self.__str__())

    def pl_ify(self):
        return self.name

    @classmethod
    def generate_atomics_set(cls, number_of: int, start_at='A'):
        if number_of <= 0:
            return []
        elif number_of <= 26:
            return [
                Atom(chr(ord(start_at) + i)) for i in range(number_of)
            ]
        else:
            raise NotImplementedError("Not Implemented. "
                                      "[Propositional.logical.Atom.generate_atomics_set]")


class LogicalConnective(Evaluable):
    def __init__(self, *components: Evaluable,
                 exempt_bin_rest=False, overfull_method='reject', under_full_method='reject'):
        """
        Create a generic logical connective.

        :param components: The sub-components (as logical connectives or logical atoms) that act
            as input to this logical connective.
        :param exempt_bin_rest: Is this logical connective exempt from being constrained to being
            a binary operation?
        :param overfull_method: How should extra components be handled when enforcing the binary
            property? Default is 'reject', although 'prune' is also accepted (Take only the first
            two elements).
        :param under_full_method: How should existence components be used to fill blank places
            when enforcing the binary property? Default is 'reject', although 'duplicate' is also
            accepted (repeat elements until we have enough).
        """
        super(LogicalConnective, self).__init__("Generic")

        self.components = components
        self.truth_table_cached = None
        self.truth_hash_cached = None

        if ENFORCE_BINARY_OPERATIONS and not exempt_bin_rest:
            # enforcing binary, not exempt, therefore check.
            # are we overfull or under full?
            num_components = len(components)
            if num_components < 2:
                # under full
                if under_full_method == 'duplicate' and num_components > 0:
                    # components has exactly 1 element.
                    self.components = [components[0], components[0]]
                elif under_full_method == 'reject':
                    raise LogicalException("Under full components box.")
            elif num_components > 2:
                # overfull
                if overfull_method == 'prune':
                    self.components = components[:2]
                elif overfull_method == 'reject':
                    raise LogicalException("Overfull components box.")

        self.exempt = exempt_bin_rest
        self.func = None

    def __bool__(self):
        if self.func is None:
            return False
        truth_values = [bool(c) for c in self.components]
        return self.func(*truth_values)

    def replace(self, old: Union[list[Evaluable], Evaluable] = None,
                new: Evaluable = None,
                lst: list[tuple[Evaluable, Evaluable]] = None):
        if type(old) is list:
            if lst is None:
                lst = old[::]
            else:
                lst += old[::]
            old = None
        if lst is None and (old is None or new is None):
            return self.copy()
        if lst is not None and old is not None and new is not None:
            lst: list[tuple[Evaluable, Evaluable]]
            lst.append((old, new))
        if lst is None:
            lst = [(old, new)]

        for old_l, new_l in lst:
            if self == old_l:
                return new_l.copy()

        self_copy = self.copy()

        self.components: list[LogicalConnective]
        self_copy.components = [
            component.replace(lst=lst)
            for component in self.components
        ]

        return self_copy

    def copy(self):
        new_components = [
            component.copy() for component in self.components
        ]
        new_log = LogicalConnective(*new_components, exempt_bin_rest=self.exempt)
        new_log.func = self.func
        new_log.name = self.name
        return new_log

    def search(self, form: Evaluable):
        """
        Where replace(A, B) will replace all instances of A with B in the current object, we are
        searching for a form. Therefore we should return None if the form is non applicable, but
        if it is, we should get a list of tuples:

        [(o_1, n_1), (o_2, n_2), ... ]

        such that if we replaced all o_i's with n_i's in 'form', we'd have 'self'
        """

        if type(form) is Atom:
            return [(form.copy(), self.copy())]

        form: LogicalConnective

        if form.name != self.name:
            return []
        if len(form.components) != len(self.components):
            return []

        forms = []

        for i in range(len(self.components)):
            form_c = form.components[i]
            self_c = self.components[i]

            if type(form_c) is Atom:
                forms.append((form_c, self_c))
                continue

            for form_i, value_i in self_c.search(form_c):
                for form_contained, value_contained in forms:
                    if form_i == form_contained:
                        if value_i == value_contained:
                            break
                        return []
                else:
                    forms.append((form_i, value_i))

        return forms

    def atoms_contained(self):
        atoms = []

        for component in self.components:
            if type(component) is Atom:
                if component not in atoms:
                    atoms.append(component)
            else:
                component: LogicalConnective

                for atom in component.atoms_contained():
                    if atom not in atoms:
                        atoms.append(atom)

        return atoms

    def set_atom_truth_values(self, context):
        try:
            for component in self.components:
                component.set_atom_truth_values(context)
        except AttributeError:
            print("Error", self)

    def truth_table(self, atomics: list[Atom] = None, regen: bool = False):
        if atomics is None:
            atomics = self.atoms_contained()
            regen = True

        if self.truth_table_cached is not None:
            atoms = [
                elem[0].name for elem in self.truth_table_cached[0][0]
            ]
            if set(atoms) != set([a.name for a in atomics]):
                regen = True

        if self.truth_table_cached is None or regen:
            truth_table = []
            for i in range(2 ** len(atomics)):
                context = {atomics[a]: (i & 1 << a) != 0 for a in range(len(atomics))}
                self.set_atom_truth_values(context)

                lst = []
                names = []
                for k in sorted(list(context.keys())):
                    if k.name not in names:
                        lst.append((Atom(k.name), context[k]))
                        names.append(k.name)

                truth_table.append(
                    (lst, bool(self))
                )

            self.truth_table_cached = truth_table
        return self.truth_table_cached

    def truth_hash(self, atomics, regen=False):
        if self.truth_hash_cached is None or regen:
            truth = self.truth_table(atomics, regen)

            truth = [
                (sorted(elem[0], key=lambda x: x[0]), elem[1]) for elem in truth
            ]

            truth = [
                (sum([
                    (1 << i if elem[0][i][1] else 0) for i in range(len(atomics))
                ]), elem[1]) for elem in truth
            ]

            truth = sorted(truth, key=lambda x: x[0])

            t_hash = ([
                    (1 << i if truth[i][1] else 0) for i in range(len(truth))
                ])

            self.truth_hash_cached = sum(t_hash)
        return self.truth_hash_cached

    def pl_ify(self):
        for key in LOGICAL_SYMBOLS.keys():
            if LOGICAL_SYMBOLS[key] == self.name:
                keyword = key
                break
        else:
            raise LogicalException(f"Couldn't find {self.name} in logical symbol set..")

        component_strings = [component.pl_ify() for component in self.components]

        if keyword == 'not':
            return f'(not {component_strings[0]})'
        else:
            return f'({component_strings[0]} {keyword} {component_strings[1]})'

    def __eq__(self, other):
        if not issubclass(type(other), LogicalConnective):
            return False

        if self.name != other.name:
            return False

        if len(self.components) != len(other.components):
            return False

        for i in range(len(self.components)):
            if self.components[i] != other.components[i]:
                return False

        return True

    def __str__(self):
        component_str = ", ".join([str(x).split(":")[0] for x in self.components])

        if ENFORCE_BINARY_OPERATIONS and not self.exempt:
            return "(" + \
                   str(self.components[0]).split(":")[0] + \
                   " " + str(self.name) + " " + \
                   str(self.components[1]).split(":")[0] + \
                   ")"
        return f"{self.name}{component_str}"

    def __repr__(self):
        return str(self)
    
    def __hash__(self):
        return hash(self.__str__())

    @staticmethod
    def is_instance(instance, name):
        if name not in list(LOGICAL_SYMBOLS.keys()):
            return False

        return str(instance.name) == str(LOGICAL_SYMBOLS[name])


def __generate_connective__(name: str, func: Callable = None, **kwargs):
    """
    Generate logical connective from name, a function that takes some
    number of boolean values and computes a new boolean. All keyword
    arguments are passed to the superclass LogicalConnective.

    :param name: Name / Symbol of the logical connective.
    :param func: Function f: [bool]^k -> bool.
    :param kwargs: LogicalConnective keyword arguments.
    :return: the generic logical connective defined.
    """

    if func is None:
        func = {
            'or': lambda x, y: x or y,
            'and': lambda x, y: x and y,
            'implies': lambda x, y: (not x) or y,
            'iff': lambda x, y: x is y,
            'not': lambda x: not x,
        }.get(name, None)
        if name == 'not':
            kwargs.update({'exempt_bin_rest': True})
        name = LOGICAL_SYMBOLS[name]

    class GenericLogical(LogicalConnective):
        def __init__(self, *components: Union[Evaluable]):
            super().__init__(*components, **kwargs)
            self.name = name
            self.func = func

        def __bool__(self):
            truth_values = [bool(c) for c in self.components]
            return func(*truth_values)

        def __str__(self):
            return super().__str__()

        def __repr__(self):
            return super().__str__()

    return GenericLogical


LOGICAL_CONNECTIVES = {
    name: __generate_connective__(name) for name in LOGICAL_SYMBOLS.keys()
}


def parse_logical(str_repr: str, surround_atoms: bool = True,
                  expect_none: bool = False) -> Union[Evaluable, LogicalConnective, Atom]:
    """
    Parse logical propositions in text format. All atomic values must use upper case characters,
    while all other characters should be lowercase.

    :param str_repr: The string to parse.
    :param surround_atoms: Whether or not to surround atomic propositions with parentheses.
                           This is necessary initially, to ensure
    :param expect_none:
    :return:
    """
    if surround_atoms:
        return parse_logical("".join([
            "(" + char + ")" if char.isupper() else char for char in str_repr
        ]), surround_atoms=False)

    if len(str_repr) == 0:
        if expect_none:
            # return none, but of evaluable type.
            return Atom("None", truth_value=False)
        else:
            raise LogicalException("0 length string.")

    depth = [
        len(sub.replace(")", "")) - len(sub.replace("(", ""))
        for sub in [
            str_repr[:i] for i in range(len(str_repr)+1)
        ]
    ]

    if -1 in depth:
        raise LogicalException("Unbalanced parentheses! Extra closing parentheses.")
    if 0 != depth[-1]:
        raise LogicalException("Unbalanced parentheses! Missing closing parentheses.")

    if len([0 for d in depth if d == 0]) == 2 and depth[0] == 0 and depth[-1] == 0:
        new_str = str_repr[1:-1]
        if len(new_str) == 1:
            return Atom(new_str)
        else:
            return parse_logical(str_repr[1:-1], surround_atoms=False)

    zero_depth_strings = [["", 0]]

    flag = True
    for i in range(len(str_repr)):
        if depth[i+1] == 0 and depth[i] == 0:
            flag = True
            zero_depth_strings[-1][0] += str_repr[i]
        else:
            if flag:
                flag = False
                zero_depth_strings.append(["", i])
            else:
                zero_depth_strings[-1][1] = i+1

    zero_depth_strings = [[string[0].strip(),
                           string[1] + (len(string[0]) - len(string[0].lstrip()))]
                          for string in zero_depth_strings
                          if len(string[0].strip()) > 0]

    if len(zero_depth_strings) != 1:
        raise LogicalException("Only one connective allowed in each set of parentheses.")

    operation = zero_depth_strings[0][0]

    sections = [
        parse_logical(str_repr[: zero_depth_strings[0][1]].strip(),
                      surround_atoms=False, expect_none=(operation == 'not')),
        parse_logical(str_repr[len(zero_depth_strings[0][0]) +
                               zero_depth_strings[0][1]:].strip(), surround_atoms=False)
    ]

    if operation == "not":
        if sections[0] is not None and sections[0] != Atom("None", truth_value=False):
            raise LogicalException("'Not' preceded by sentence.")
        return ~sections[1]
    elif operation in LOGICAL_SYMBOLS.keys():
        return LOGICAL_CONNECTIVES[operation](sections[0], sections[1])
    else:
        raise LogicalException(f"Unrecognized operation: {operation}")
