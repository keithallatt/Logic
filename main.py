from Propositional.logical import *
PL = parse_logical

if __name__ == '__main__':
    atomics = [
        PL(chr(i)) for i in range(ord("A"), ord("C")+1)
    ]

    print(atomics)
