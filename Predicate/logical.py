from __future__ import annotations
from Propositional.logical import LogicalException

PREDICATE_SYMBOLS = {
    'forall': u'\u2200',
    'exists': u'\u2203',
    'exists unique': u'\u2203!',
}

MATH_SYMBOLS = {
    'times': u'\u00D7',
}


class Predicate:
    def evaluate(self, context: dict):
        pass

    def __str__(self):
        pass


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


class Equality(Predicate):
    def __init__(self, lhs: Term, rhs: Term):
        self.lhs = lhs
        self.rhs = rhs

    def evaluate(self, context: dict):
        return self.lhs.interpret(context) == self.rhs.interpret(context)

    def __str__(self):
        return f"({str(self.lhs)} = {str(self.rhs)})"


class Quantifier(Predicate):
    def __init__(self, sub_pred: Predicate, variable: Variable, domain: list = None):
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


if __name__ == '__main__':
    x = Variable('x')
    y = Variable('y')
    times = Function(MATH_SYMBOLS['times'], [x, y], notation='infix')
    context_ = {
        MATH_SYMBOLS['times']: lambda x_, y_: x_ * y_,
        'x': 3,
        'y': 4
    }

    print(times.interpret(context_))
