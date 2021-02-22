from __future__ import annotations
# going to need this, for logical connectives.
from Propositional.logical import *


class Predicate:
    def evaluate(self, context: dict):
        return None

    def __str__(self):
        pass


class Sentence:
    def interpret(self, context: dict):
        pass


class Variable(Sentence):
    def __init__(self, variable_name: str):
        self.variable_name = variable_name

    def interpret(self, context: dict):
        return context.get(self.variable_name, None)

    def __str__(self):
        return self.variable_name


class Equality(Predicate):
    def __init__(self, lhs: Sentence, rhs: Sentence):
        self.lhs = lhs
        self.rhs = rhs

    def evaluate(self, context: dict):
        return self.lhs.interpret(context) == self.rhs.interpret(context)

    def __str__(self):
        return str(self.lhs) + " = " + str(self.rhs)


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


def models(context: list, pred: Predicate):
    pass


if __name__ == '__main__':
    context_set = [
        0, 1, 2, 3, 4
    ]

    x, y = Variable("x"), Variable("y")

    eq = Equality(x, y)

    un1 = Existential(eq, x, domain=context_set)
    un2 = Existential(un1, y, domain=context_set)

    print(un2.evaluate({}))
