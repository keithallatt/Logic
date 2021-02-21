from Propositional.derivations import *


class BFSDirectDerivation:
    """ Use B.F.S. to find a proof for a logical derivation. """
    def __init__(self, axioms: list[Evaluable], goal_proposition: Evaluable):
        self.axioms = axioms
        self.consequence = goal_proposition

    def search(self):

        if type(self.consequence) is LogicalImplies:
            d = ConditionalDerivation(self.axioms, self.consequence, [])
        else:
            d = DirectDerivation(self.axioms, self.consequence, [])

        if not d.is_valid():
            raise LogicalException("Cannot search for proof in invalid argument." +
                                   "Counter example: " + str(d.get_counter_example()))

        environment = {ax: [] for ax in d.axioms}
        environment.update({ax: [] for ax in d.assumptions})

        while True:
            new_environment = {}
            max_depth = max([arg.num_inputs for arg in DERIVATIONS])

            def gen_env_tuples(depth: int):
                if depth == 1:
                    return [(env,) for env in environment.items()]

                return [
                    (env, *tup) for env in environment.items() for tup in gen_env_tuples(depth-1)
                ] + gen_env_tuples(depth-1)

            env_tuples = gen_env_tuples(max_depth)

            for argument in DERIVATIONS:
                for env_tup in env_tuples:
                    con, path = [env[0] for env in env_tup], [env[1] for env in env_tup]

                    if argument.num_inputs != len(con):
                        # should not work if not right number of parameters
                        continue

                    arg = argument(*con)

                    try:

                        new_path = sum(path, []) + [arg]
                        application = arg.apply()

                        if application == d.consequence:
                            return new_path

                        # if apply works

                        # if distinct from all before it.
                        for e_c in environment.items():
                            if e_c[0] == application:
                                continue
                        for e_c in new_environment.items():
                            if e_c[0] == application:
                                continue

                        # add to environment

                        new_environment.update({application: new_path})

                    except LogicalException:
                        pass

            if new_environment == {}:
                return []

            environment.update(new_environment)


if __name__ == '__main__':
    PL = parse_logical

    axiom_sets = [
        [
            PL("A"), PL("not C"), PL("(A implies (B implies C))")
        ],
        [
            PL("A implies B"), PL("B implies C")
        ]

    ]
    consequence_set = [
        PL("not B"),
        PL("A implies C")
    ]

    derivation_sets = [
        [
            ModusPonens(PL("A"), PL("(A implies (B implies C))")),
            ModusTollens(PL("B implies C"), PL("not C"))
        ],
        [
            ModusPonens(PL("A"), PL("A implies B")),
            ModusPonens(PL("B"), PL("B implies C"))
        ]
    ]

    for axiom, consequence, derivation in zip(axiom_sets, consequence_set, derivation_sets):
        derivation_type = DirectDerivation
        if type(consequence) is LogicalImplies:
            derivation_type = ConditionalDerivation

        p1 = derivation_type(
            axiom,
            consequence,
            derivation
        )

        print("Handwritten Proof")
        print("---------")

        print("\n\t".join([""] + (p1verification := p1.verify()).split("\n"))[1:])
        print("---------")

        bfs = BFSDirectDerivation(
            axiom,
            consequence
        )

        derivation2 = bfs.search()

        p2 = derivation_type(
            axiom,
            consequence,
            derivation2
        )

        print("---------")
        print("Computer Generated Proof")
        print("---------")

        print("\n\t".join([""] + (p2verification := p2.verify()).split("\n"))[1:])
        print("---------")

        # print(f"Proof is identical: {p1verification == p2verification}")
        print("---------")
