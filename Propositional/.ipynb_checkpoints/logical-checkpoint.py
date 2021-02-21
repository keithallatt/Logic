from __future__ import annotations
from abc import abstractmethod
from typing import Union, Callable
import warnings

# Unicode logical symbols (propositional logic)
LOGICAL_SYMBOLS = {
    "and": u'\u2227',
    "or": u'\u2228',
    "implies": u'\u2192',
    "iff": u'\u2194',
    "not": u'\u00AC',
    "proves": u'\u22A2',
    "models": u'\u22A8'
}


class LogicalException(Exception):
    """ Exception relating to logical mistakes. """
    def __init__(self, cause=None):
        super().__init__(cause)
        self.logical_cause = cause


# enforce that logical connectives must be binary, unless exempt.
# if this is false, then any connective can have any number of parameters.
ENFORCE_BINARY_OPERATIONS = True


class Evaluable:
    """ A boolean evaluable expression. """
    @abstractmethod
    def __bool__(self):
        pass

    def __and__(self, other):
        return LogicalAnd(self, other)
    
    def __rand__(self, other):
        return self.__and__(other)
    
    def __or__(self, other):
        return LogicalOr(self, other)
    
    def __ror__(self, other):
        return self.__or__(other)
    
    def __invert__(self):
        return LogicalNot(self)

    def __rshift__(self, other):
        return LogicalImplies(self, other)

    def __lshift__(self, other):
        return LogicalImplies(other, self)

    def __xor__(self, other):
        return LogicalIff(self, other)


class Atom(Evaluable):
    """ Logical Atom. Represents a variable / truth value.
        This is the smallest unit in 0th order logic. """
    def __init__(self, name: str, truth_value: bool = None):
        self.truth_value = truth_value
        self.name = name

    def __bool__(self):
        if self.truth_value is None:
            return False
        return self.truth_value
    
    def set_atom_truth_values(self, context):
        for c in context.keys():
            if c.name == self.name:
                self.truth_value = context[c]
                break
        else:
            raise LogicalException("Missing key:" + str(self))

    def __eq__(self, other):
        return type(other) == Atom and \
               self.name == other.name and \
               (self.truth_value == other.truth_value or
                self.truth_value is None or
                other.truth_value is None)

    def __str__(self):
        return self.name
    
    def __repr__(self):
        return str(self)

    def __lt__(self, other):
        if type(other) is Atom:
            return self.name < other.name
        else:
            return False

    def __hash__(self):
        return hash(self.__str__())


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

        self.components = components

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

        self.name = "Generic"
        self.exempt = exempt_bin_rest

    @abstractmethod
    def __bool__(self):
        pass

    def replace(self, old: Evaluable, new: Evaluable):
        pass

    def atoms_contained(self):
        atoms = []

        for component in self.components:
            if type(component) is Atom:
                atoms.append(component)
            else:
                component: LogicalConnective
                atoms += component.atoms_contained()

        atoms = [
            atoms[i] for i in range(len(atoms)) if atoms.index(atoms[i]) == i
        ]

        return atoms

    def set_atom_truth_values(self, context):
        for component in self.components:
            component.set_atom_truth_values(context)

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

    def __str__(self, parentheses=False):
        component_str = ", ".join([str(x).split(":")[0] for x in self.components])

        if ENFORCE_BINARY_OPERATIONS and not self.exempt:
            return "(" + \
                   str(self.components[0]).split(":")[0] + \
                   " " + self.name + " " + \
                   str(self.components[1]).split(":")[0] + \
                   ")"
        return f"{self.name}{component_str}"

    def __repr__(self):
        return str(self)
    
    def __hash__(self):
        return hash(self.__str__())


def __generate_connective__(name: str, func: Callable, **kwargs):
    """
    Generate logical connective from name, a function that takes some
    number of boolean values and computes a new boolean. All keyword
    arguments are passed to the superclass LogicalConnective.

    :param name: Name / Symbol of the logical connective.
    :param func: Function f: [bool]^k -> bool.
    :param kwargs: LogicalConnective keyword arguments.
    :return: the generic logical connective defined.
    """
    class GenericLogical(LogicalConnective):
        def __init__(self, *components: Union[Evaluable]):
            super().__init__(*components, **kwargs)
            self.name = name

        def __bool__(self):
            truth_values = [bool(c) for c in self.components]
            return func(*truth_values)

        def __str__(self):
            return super().__str__()

        def __repr__(self):
            return super().__str__()

    return GenericLogical


LogicalOr = __generate_connective__(LOGICAL_SYMBOLS["or"], lambda x, y: x or y)
LogicalAnd = __generate_connective__(LOGICAL_SYMBOLS["and"], lambda x, y: x and y)
LogicalImplies = __generate_connective__(LOGICAL_SYMBOLS["implies"], lambda x, y: (not x) or y)
LogicalIff = __generate_connective__(LOGICAL_SYMBOLS["iff"], lambda x, y: not (x ^ y))
LogicalNot = __generate_connective__(LOGICAL_SYMBOLS["not"], lambda x: not x, exempt_bin_rest=True)


def parse_logical(str_repr: str,
                  surround_atoms: bool = True,
                  expect_none: bool = False) -> Evaluable:
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
        raise LogicalException("Only one connective allowed at each depth.")

    operation = zero_depth_strings[0][0]

    sections = [
        parse_logical(str_repr[: zero_depth_strings[0][1]].strip(),
                      surround_atoms=False, expect_none=(operation == 'not')),
        parse_logical(str_repr[len(zero_depth_strings[0][0]) +
                               zero_depth_strings[0][1]:].strip(), surround_atoms=False)
    ]

    if operation == "and":
        return LogicalAnd(sections[0], sections[1])
    elif operation == "or":
        return LogicalOr(sections[0], sections[1])
    elif operation == "implies":
        return LogicalImplies(sections[0], sections[1])
    elif operation == "iff":
        return LogicalIff(sections[0], sections[1])
    elif operation == "not":
        if sections[0] is not None and sections[0] != Atom("None", truth_value=False):
            raise LogicalException("'Not' preceded by sentence.")
        return LogicalNot(sections[1])
    else:
        raise LogicalException(f"Unrecognized operation: {operation}")


if __name__ == '__main__':
    print(parse_logical("B and (A or B)"))
