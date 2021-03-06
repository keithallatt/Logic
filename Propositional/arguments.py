from Propositional.logical import *
import warnings
import inspect
import sys

# https://en.wikipedia.org/wiki/Propositional_calculus


class Argument:
    """ An argument is a list of propositions. We say C follows from any set of propositions
        (P_1, ..., P_n), if C must be true whenever all P_i are true (1 <= i <= n). """
    num_inputs = 0

    def __init__(self, argument_name, *ls: Evaluable):
        self.ls = ls
        self.argument_name = argument_name

    def __str__(self):
        arg_name = ''.join([c for c in self.argument_name if c not in ".'"])

        arg_name = ' '.join([word.capitalize() for word in arg_name.split(' ')])

        return arg_name + ": {" + \
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
    def get_application(self) -> Union[Evaluable, None]:
        """ Get the consequence of this argument. (I.e. return C) """
        pass

    def apply(self):
        """ Return the consequence if the argument is sound (propositions true). """
        if (application := self.get_application()) is not None:
            return application
        else:
            raise LogicalException(f"No application of {self.argument_name} found.")

    def required_propositions(self):
        """ Not all arguments require that all components are true. For example,
            (A ⊢ A ∨ B), but to write the argument, we write Addition(A, A | B), but
            A ∨ B is a consequence, so not required. For some arguments, this is not
            necessary, so by default all Evaluable's input """
        return self.ls


class Contradiction(Argument):
    """ p; not p; therefore q """
    num_inputs = 2

    def __init__(self, p: Evaluable, not_p: Evaluable):
        super().__init__("Contradiction", p, not_p)

    def get_application(self) -> Union[Evaluable, None]:
        p, not_p = self.ls[:2]
        if p == ~not_p or ~p == not_p:
            raise LogicalException("Contradiction")
        return None

    def required_propositions(self):
        return self.ls[:2]


class Assumption(Argument):
    """ Assume p; """
    num_inputs = 1

    def __init__(self, l1: Evaluable):
        super().__init__("ASsuMption", l1)

    def get_application(self) -> Union[Evaluable, None]:
        return self.ls[0]

    def required_propositions(self):
        return []


class Repeat(Argument):
    """ p; therefore p """
    num_inputs = 1

    def __init__(self, l1: Evaluable):
        super().__init__("Repetition", l1)

    def get_application(self) -> Union[Evaluable, None]:
        return self.ls[0]


class ModusPonens(Argument):
    """ If p then q; p; therefore q """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Modus Ponens", l1, l2)

    def get_application(self) -> Union[Evaluable, None]:
        logical_implies = LOGICAL_CONNECTIVES['implies']
        l1, l2 = self.ls[:2]
        if type(l1) is logical_implies:
            l1: LogicalConnective
            premise = l1.components[0]
            consequence = l1.components[1]

            if premise == l2:
                return consequence
        if type(l2) is logical_implies:
            l2: LogicalConnective
            premise = l2.components[0]
            consequence = l2.components[1]

            if premise == l1:
                return consequence
        return None


class ModusTollens(Argument):
    """ If p then q; not q; therefore not p """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Modus Tollens", l1, l2)

    def get_application(self) -> Union[Evaluable, None]:
        logical_implies = LOGICAL_CONNECTIVES['implies']
        l1, l2 = self.ls[:2]
        if type(l1) is logical_implies:
            l1: LogicalConnective
            premise = l1.components[0]
            consequence = l1.components[1]

            if ~consequence == l2 or consequence == ~l2:
                return ~premise
        if type(l2) is logical_implies:
            l2: LogicalConnective
            premise = l2.components[0]
            consequence = l2.components[1]

            if ~consequence == l1 or consequence == ~l1:
                return ~premise

        return None


class HypotheticalSyllogism(Argument):
    """ If p then q; if q then r; therefore, if p then r """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Modus Tollens", l1, l2)

    def get_application(self) -> Union[Evaluable, None]:
        logical_implies = LOGICAL_CONNECTIVES['implies']
        l1, l2 = self.ls[:2]
        if type(l1) is logical_implies and type(l2) is logical_implies:
            p = l1.components[0]
            q1 = l1.components[1]
            q2 = l2.components[0]
            r = l2.components[1]
            if q1 == q2:
                return p >> r
        return None


class ModusTollendoPonens(Argument):
    """ Either p or q, or both; not p; therefore, q """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Modus Tollendo Ponens", l1, l2)

    def get_application(self) -> Union[Evaluable, None]:
        logical_or = LOGICAL_CONNECTIVES['or']
        l1, l2 = self.ls[:2]

        if type(l1) is logical_or:
            p, q = l1.components[:2]

            if l2 == ~p or p == ~l2:
                return q
            if l2 == ~q or q == ~l2:
                return p

        if type(l2) is logical_or:
            p, q = l2.components[:2]

            if l1 == ~p or p == ~l1:
                return q
            if l1 == ~q or q == ~l1:
                return p
        return None


class Conjunction(Argument):
    """ p, q; therefore p and q """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Simplification", l1, l2)
        self.get_application()

    def get_application(self) -> Union[Evaluable, None]:
        l1, l2 = self.ls[:2]
        return l1 & l2


class Simplification(Argument):
    """ p and q; therefore p / p and q; therefore q """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Simplification", l1, l2)
        self.rp = []
        self.get_application()

    def get_application(self) -> Union[Evaluable, None]:
        logical_and = LOGICAL_CONNECTIVES['and']
        l1, l2 = self.ls[:2]

        if type(l1) is logical_and:
            p, q = l1.components[:2]

            if l2 == p:
                self.rp = [l1]
                return l2
            if l2 == q:
                self.rp = [l1]
                return l2
        if type(l2) is logical_and:
            p, q = l2.components[:2]

            if l1 == p:
                self.rp = [l2]
                return l1
            if l1 == q:
                self.rp = [l2]
                return l1
        return None

    def required_propositions(self):
        return self.rp


class Addition(Argument):
    """ p; therefore p or q / q; therefore p or q """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Addition", l1, l2)

    def get_application(self) -> Union[Evaluable, None]:
        logical_or = LOGICAL_CONNECTIVES['or']
        l1, l2 = self.ls[:2]

        if type(l1) is logical_or:
            p, q = l1.components[:2]

            if l2 == p:
                return l1
            if l2 == q:
                return l1
        if type(l2) is logical_or:
            p, q = l2.components[:2]

            if l1 == p:
                return l2
            if l1 == q:
                return l2
        return None

    def required_propositions(self):
        return self.ls[:1]


class DoubleNegation(Argument):
    """ p; therefore not not p / not not p; therefore p """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Double Negation", l1, l2)

    def get_application(self) -> Union[Evaluable, None]:
        l1, l2 = self.ls[:2]

        if l1 == ~~l2 or ~~l1 == l2:
            return l2
        return None

    def required_propositions(self):
        return self.ls[:1]


class BidirectionalConditional(Argument):
    """ p iff q; therefore p implies q /
        p iff q; therefore q implies p /
        p implies q; q implies p; therefore p iff q """
    num_inputs = 2

    def __init__(self, l1: Evaluable, l2: Evaluable):
        super().__init__("Bidirectional Conditional", l1, l2)
        self.rp = []
        self.get_application()

    def get_application(self) -> Union[Evaluable, None]:
        logical_iff = LOGICAL_CONNECTIVES['iff']
        logical_implies = LOGICAL_CONNECTIVES['implies']
        l1, l2 = self.ls[:2]

        if type(l1) is logical_iff and type(l2) is logical_implies:
            # first two are elimination
            p1, q1 = l1.components[:2]
            p2, q2 = l2.components[:2]

            if p1 == p2 and q1 == q2:
                self.rp = [l1]
                return l2
            if p1 == q2 and q1 == p2:
                self.rp = [l1]
                return l2
        if type(l2) is logical_iff and type(l1) is logical_implies:
            # elimination
            p1, q1 = l1.components[:2]
            p2, q2 = l2.components[:2]

            if p1 == p2 and q1 == q2:
                self.rp = [l2]
                return l1
            if p1 == q2 and q1 == p2:
                self.rp = [l2]
                return l1
        if type(l1) is logical_implies and type(l2) is logical_implies:
            # introduction
            p1, q1 = l1.components[:2]
            p2, q2 = l2.components[:2]
            if p1 == q2 and q1 == p2:
                self.rp = [l1, l2]
                return p1 ^ q1
        return None

    def required_propositions(self):
        return self.rp


# GLOBAL VARIABLE BLOB
DERIVATIONS = [
    class_type for (class_name, class_type) in
    inspect.getmembers(sys.modules[__name__], inspect.isclass)
    if issubclass(class_type, Argument) and class_type != Argument
]
