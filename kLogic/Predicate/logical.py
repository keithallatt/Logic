from __future__ import annotations
from typing import Union
from kLogic.Propositional.logical import LogicalException, LOGICAL_SYMBOLS, LOGICAL_CONNECTIVES
# relative import
from kLogic import symbolic

PREDICATE_SYMBOLS = symbolic.PredicateSymbolSet()
MATH_SYMBOLS = symbolic.MathSymbolSet()

# Predicates

class Predicate:
    """ Logical Predicate in FOL. """
    def __init__(self):
        """ Create an arbitrary predicate object """
        pass

    def __and__(self, other):
        """ Returns (self and other) """
        return PREDICATE_CONNECTIVES['and'](self, other)

    def __rand__(self, other):
        """ Returns (self and other) """
        return self.__and__(other)

    def __or__(self, other):
        """ Returns (self or other) """
        return PREDICATE_CONNECTIVES['or'](self, other)

    def __ror__(self, other):
        """ Returns (self or other) """
        return self.__or__(other)

    def __invert__(self):
        """ Returns (not self) """
        return PREDICATE_CONNECTIVES['not'](self)

    def __rshift__(self, other):
        """ Returns (self implies other) """
        return PREDICATE_CONNECTIVES['implies'](self, other)

    def __lshift__(self, other):
        """ Returns (self if other) """
        return PREDICATE_CONNECTIVES['implies'](other, self)

    def __xor__(self, other):
        """ Returns (self if and only if other) """
        return PREDICATE_CONNECTIVES['iff'](self, other)

    def evaluate(self, context: dict):
        """ Evaluate a predicate and return a boolean. """
        pass

    def __str__(self):
        pass


class Equality(Predicate):
    """ Defines an equality relation (the basic relation included in FOL)
        x = y if and only if x^M = y^M in the context M (where x^M, y^M are
        the interpretations of x and y in the context set M). """
    def __init__(self, lhs: Term, rhs: Term):
        super().__init__()
        self.lhs = lhs
        self.rhs = rhs

    def evaluate(self, context: dict):
        return self.lhs.interpret(context) == self.rhs.interpret(context)

    def __str__(self):
        return f"({str(self.lhs)} = {str(self.rhs)})"


# Logical Connectives

def __generate_connective__(name: str):
    """
        Generate a FOL logical connective, such as the propositional logic
        connectives.
    """
    name, connective = LOGICAL_SYMBOLS[name], LOGICAL_CONNECTIVES[name]

    class GenericPredicate(Predicate):
        def __init__(self, *components: Union[Predicate]):
            super().__init__()
            self.connective = connective(*components)
            self.components = components

        def evaluate(self, context: dict):
            truth_values = [c.evaluate(context) for c in self.components]
            return self.connective.func(*truth_values)

        def __str__(self):
            return str(self.connective)

        def __repr__(self):
            return super().__str__()

    return GenericPredicate


PREDICATE_CONNECTIVES = {
    name: __generate_connective__(name) for name in LOGICAL_SYMBOLS.keys()
}


# Terms

class Term:
    """  """
    def interpret(self, context: dict):
        pass


class Variable(Term):
    def __init__(self, variable_name: str):
        self.variable_name = variable_name

    def interpret(self, context: dict):
        return context.get(self.variable_name, None)

    def __str__(self):
        return self.variable_name


class Function(Term):
    def __init__(self, function_name: str, terms: list[Term], notation='prefix'):
        """

        :param function_name: name / symbol of function (R, ×, etc.)
        :param terms: the terms being fed as input to this function.
        :param notation: either prefix ( R(x, y) ) or infix (x × y), or polish ( f x y )
        """
        self.function_name = function_name
        self.terms = terms
        self.arity = len(terms)
        self.notation = notation

    def interpret(self, context: dict):
        interpretation = context.get(self.function_name)
        if callable(interpretation):
            return interpretation(*[term.interpret(context) for term in self.terms])
        else:
            raise LogicalException(f"Interpretation of {self.function_name} not callable.")

    def __str__(self):
        if self.notation.lower() == 'prefix':
            term_group = ", ".join([str(term) for term in self.terms])
            return f"{self.function_name}({term_group})"
        elif self.notation.lower() == 'polish':
            term_group = " ".join([str(term) for term in self.terms])
            return f"{self.function_name} {term_group}"
        elif self.notation.lower() == 'infix':
            if self.arity != 2:
                self.notation = 'prefix'
                return str(self)
            return f"({str(self.terms[0])} {self.function_name} {str(self.terms[1])})"
        else:
            self.notation = 'prefix'
            return str(self)


# Relations

class Relation(Predicate):
    def __init__(self):
        super().__init__()


# Quantifiers

class Quantifier(Predicate):
    def __init__(self, sub_pred: Predicate, variable: Variable, domain: list = None):
        super().__init__()
        self.sub_predicate = sub_pred
        self.variable = variable
        self.domain = domain


class Universal(Quantifier):
    def __init__(self, sub_pred: Predicate, variable: Variable, domain: list = None):
        super().__init__(sub_pred, variable, domain)

    def evaluate(self, context: dict):
        sub_context = {k: v for k, v in context.items()}
        for element in self.domain:
            sub_context.update({self.variable.variable_name: element})

            if not self.sub_predicate.evaluate(sub_context):
                return False
        return True

    def __str__(self):
        return f"({PREDICATE_SYMBOLS['forall']} {self.variable}){str(self.sub_predicate)}"


class Existential(Quantifier):
    def __init__(self, sub_pred: Predicate, variable: Variable, domain: list = None):
        super().__init__(sub_pred, variable, domain)

    def evaluate(self, context: dict):
        sub_context = {k: v for k, v in context.items()}
        for element in self.domain:
            sub_context.update({self.variable.variable_name: element})

            if self.sub_predicate.evaluate(sub_context):
                return True
        return False

    def __str__(self):
        return f"({PREDICATE_SYMBOLS['exists']} {self.variable}){str(self.sub_predicate)}"


class UniqueExistential(Quantifier):
    def __init__(self, sub_pred: Predicate, variable: Variable, domain: list = None):
        super().__init__(sub_pred, variable, domain)

    def evaluate(self, context: dict):
        sub_context = {k: v for k, v in context.items()}
        flag = False
        for element in self.domain:
            sub_context.update({self.variable.variable_name: element})

            if self.sub_predicate.evaluate(sub_context):
                if flag:
                    return False
                flag = True
        return flag

    def __str__(self):
        return f"({PREDICATE_SYMBOLS['exists unique']} {self.variable}){str(self.sub_predicate)}"


if __name__ == '__main__':
    for symbol, unicode in MATH_SYMBOLS.items():
        print(symbol, unicode, hex(ord(unicode)))

    exit(0)

    x = Variable('x')
    y = Variable('y')
    z = Variable('z')

    context_ = {
        'x': 3,
        'y': 3,
        'z': 4,
    }

    domain_ = [0, 1, 2, 2]

    eq1 = Equality(x, y)
    eq2 = Equality(y, z)
    eq3 = Equality(x, z)

    thing = (eq1 & eq2) >> eq3

    forall_z = Universal(thing, z, domain_)
    forall_y = Universal(forall_z, y, domain_)
    forall_x = Universal(forall_y, x, domain_)

    ###

    thing = Existential(UniqueExistential(Equality(x, y), y, domain_), x, domain_)

    print(thing, thing.evaluate(context={}))
