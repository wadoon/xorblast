#!/usr/bin/python3

import sys, os

def seq2str(seq, prefix=""):
    def fn(x):
        x = int(x)
        v = prefix+str(abs(x))
        if x < 0:
            return "(not %s)" % v
        else:
            return v
    return ' '.join(map(fn, seq))

VAR = 1

def as_smt(filename, prefix = "a2"):
    global VAR
    formula = "(and \n";

    with open(filename) as fp:
        lines = iter(fp)

        p, cnf, vars, clauses = next(lines).split(" ")

        for i in range(VAR, int(vars) + 1):
            print("(declare-fun %s%d () Bool)" % (prefix,i))
        VAR = int(vars) + 1


        for line in fp.readlines():
            line = line.strip()

            if line[0] == 'c' or line == '':
                continue

            if line[0] == 'x':
                C = line[2:-2].split(" ")
                formula += "\t(xor " + seq2str(C, prefix) + ")\n"
            else:
                C = line[:-2].split(" ")
                formula += "\t(or " + seq2str(C, prefix) + ")\n"
    return formula + ")"

print("""
(set-option :produce-models true)
""")
f1 = as_smt(sys.argv[1], 'a')
f2 = as_smt(sys.argv[2], 'a')

print("(assert (not (=> \n%s\n%s)))" % (f1,f2))
print("(check-sat) (get-model)")
