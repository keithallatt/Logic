from logical import *
import warnings
import inspect
import sys

# https://en.wikipedia.org/wiki/Propositional_calculus


class Argument:
    """  """
    num_inputs = 0

    def __init__(self, argument_name, *ls: Evaluable):
        self.ls = ls
        i = 1
        for component in ls:
            self.__setattr__("l"+str(i), component)
            i += 1
        self.argument_name = argument_name

    def __str__(self):
        return self.argument_name + ": {" + \
               ", ".join([str(component) for component in self.ls]) + "}"

    def __getattr__(self, name):
        """ will only get called for undefined attributes """
        warnings.warn('No member "%s" contained in settings config.' % name)
        return ''

    def __hash__(self):
        return hash(self.ls)

    def __eq__(self, other):
        if type(other) is not Argument:
            return False

        return set(self.ls) == set(other.ls)

    @abstractmethod
    def is_applicable(self) -> Union[Evaluable, None]:
        pass

    def apply(self):
        if (application := self.is_applicable()) is not None:
            return application
        else:
            raise LogicalException(f"No application of {self.argument_name} found.")

    def required_propositions(self):
        return self.ls


class Contradiction(Argument):
    """ p; not p; therefore q """
    num_inputs = 2

    def __init__(self, p: Evaluable, not_p: Evaluable):
        super().__init__("Contradiction", p, not_p)

    def is_applicable(self) -> Union[Evaluable, None]:
        p, not_p = self.ls[:2]
        if p == LogicalNot(not_p) or LogicalNot(p) == not_p:
            raise LogicalException("Contradiction")
        return None

    def required_propositions(self):
        return [self.l1, self.l2]


class Repeat(Argument):
    """ p; therefore p """
    num_inputs = 1

    def __init__(self, l1: Evaluable):
        super().__init__("Repetition", l1)

    def is_applicable(self) -> Union[Evaluable, None]:
        return self.l1


class ModusPonens(Argument):
    """ If p then q; p; therefore q """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Modus Ponens", l1, l2)

    def is_applicable(self) -> Union[Evaluable, None]:
        if type(self.l1) is LogicalImplies:
            self.l1: LogicalConnective
            premise = self.l1.components[0]
            consequence = self.l1.components[1]

            if premise == self.l2:
                return consequence
        if type(self.l2) is LogicalImplies:
            self.l2: LogicalConnective
            premise = self.l2.components[0]
            consequence = self.l2.components[1]

            if premise == self.l1:
                return consequence

        return None


class ModusTollens(Argument):
    """ If p then q; not q; therefore not p """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Modus Tollens", l1, l2)

    def is_applicable(self) -> Union[Evaluable, None]:
        if type(self.l1) is LogicalImplies:
            self.l1: LogicalConnective
            premise = self.l1.components[0]
            consequence = self.l1.components[1]

            if LogicalNot(consequence) == self.l2 or consequence == LogicalNot(self.l2):
                return LogicalNot(premise)
        if type(self.l2) is LogicalImplies:
            self.l2: LogicalConnective
            premise = self.l2.components[0]
            consequence = self.l2.components[1]

            if LogicalNot(consequence) == self.l1 or consequence == LogicalNot(self.l1):
                return LogicalNot(premise)

        return None


class HypotheticalSyllogism(Argument):
    """ If p then q; if q then r; therefore, if p then r """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Modus Tollens", l1, l2)

    def is_applicable(self) -> Union[Evaluable, None]:
        if type(self.l1) is LogicalImplies and type(self.l2) is LogicalImplies:
            p = self.l1.components[0]
            q1 = self.l1.components[1]
            q2 = self.l2.components[0]
            r = self.l2.components[1]

            if q1 != q2:
                return None

            return LogicalImplies(p, r)
        return None


class ModusTollendoPonens(Argument):
    """ Either p or q, or both; not p; therefore, q """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Modus Tollendo Ponens", l1, l2)

    def is_applicable(self) -> Union[Evaluable, None]:
        if type(self.l1) is LogicalOr:
            p, q = self.l1.components[:2]

            if self.l2 == LogicalNot(p) or p == LogicalNot(self.l2):
                return q
            if self.l2 == LogicalNot(q) or q == LogicalNot(self.l2):
                return p

        if type(self.l2) is LogicalOr:
            p, q = self.l2.components[:2]

            if self.l1 == LogicalNot(p) or p == LogicalNot(self.l1):
                return q
            if self.l1 == LogicalNot(q) or q == LogicalNot(self.l1):
                return p
        return None


class Simplification(Argument):
    """ p and q; therefore p / p and q; therefore q """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Simplification", l1, l2)
        self.rp = []
        self.is_applicable()

    def is_applicable(self) -> Union[Evaluable, None]:
        if type(self.l1) is LogicalAnd:
            p, q = self.l1.components[:2]

            if self.l2 == p:
                self.rp = [self.l1]
                return self.l2
            if self.l2 == q:
                self.rp = [self.l1]
                return self.l2
        if type(self.l2) is LogicalAnd:
            p, q = self.l2.components[:2]

            if self.l1 == p:
                self.rp = [self.l2]
                return self.l1
            if self.l1 == q:
                self.rp = [self.l2]
                return self.l1
        return None

    def required_propositions(self):
        return self.rp


class Addition(Argument):
    """ p; therefore p or q / q; therefore p or q """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Addition", l1, l2)

    def is_applicable(self) -> Union[Evaluable, None]:
        if type(self.l1) is LogicalOr:
            p, q = self.l1.components[:2]

            if self.l2 == p:
                return self.l1
            if self.l2 == q:
                return self.l1
        if type(self.l2) is LogicalOr:
            p, q = self.l2.components[:2]

            if self.l1 == p:
                return self.l2
            if self.l1 == q:
                return self.l2
        return None

    def required_propositions(self):
        return [self.l1]


class DoubleNegation(Argument):
    """ p; therefore not not p / not not p; therefore p """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Double Negation", l1, l2)

    def is_applicable(self) -> Union[Evaluable, None]:
        if self.l1 == LogicalNot(LogicalNot(self.l2)) or \
                LogicalNot(LogicalNot(self.l1)) == self.l2:
            return self.l2

        return None

    def required_propositions(self):
        return [self.l1]


class BidirectionalConditional(Argument):
    """ p iff q; therefore p implies q /
        p iff q; therefore q implies p /
        p implies q; q implies p; therefore p iff q """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Bidirectional Conditional", l1, l2)
        self.rp = []
        self.is_applicable()

    def is_applicable(self) -> Union[Evaluable, None]:
        if type(self.l1) is LogicalIff and type(self.l2) is LogicalImplies:
            # first two are elimination
            p1, q1 = self.l1.components[:2]
            p2, q2 = self.l2.components[:2]

            if p1 == p2 and q1 == q2:
                self.rp = [self.l1]
                return self.l2
            if p1 == q2 and q1 == p2:
                self.rp = [self.l1]
                return self.l2
        if type(self.l2) is LogicalIff and type(self.l1) is LogicalImplies:
            # elimination
            p1, q1 = self.l1.components[:2]
            p2, q2 = self.l2.components[:2]

            if p1 == p2 and q1 == q2:
                self.rp = [self.l2]
                return self.l1
            if p1 == q2 and q1 == p2:
                self.rp = [self.l2]
                return self.l1
        if type(self.l1) is LogicalImplies and type(self.l2) is LogicalImplies:
            # introduction
            p1, q1 = self.l1.components[:2]
            p2, q2 = self.l2.components[:2]
            if p1 == q2 and q1 == p2:
                self.rp = [self.l1, self.l2]
                return LogicalIff(p1, q1)

        return None

    def required_propositions(self):
        return self.rp


# Other arguments
# de morgans laws

# GLOBAL VARIABLE BLOB
DERIVATIONS = [
    class_type for (class_name, class_type) in
    inspect.getmembers(sys.modules[__name__], inspect.isclass)
    if issubclass(class_type, Argument) and class_type != Argument
]

if __name__ == '__main__':
    PL = parse_logical

    prop1 = PL("A implies B")
    prop2 = PL("B implies A")

    bc = BidirectionalConditional(prop2, prop1)

    print(bc.apply())
