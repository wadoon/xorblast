#!/usr/bin/python3


import random, sys, os
from random import *
from math import pi, floor

seed(floor(pi*1000))

def gen():
    vars     = randint(10,28);
    clauses  = randint(1,10);
    xclauses = randint(1,clauses);

    V = list(range(1,vars))
    L = V + list(map(lambda x: x*-1, range(1,vars)))

    print("p cnf %d %d" % (vars, clauses))

    seq2str = lambda seq: ' '.join(map(str,seq))

    for i in range(clauses):
        s = list(sample(L, randint(1, vars-1)))
        print(seq2str(s), '0')

    for i in range(xclauses):
        s = list(sample(V, randint(1, vars-1)))
        if randint(0,1):
            s[0] *= -1
        print('x',seq2str(s), '0')

for i in range(1,1000):
    with open("test_%03d.cnf" % i, 'w') as fp:
        sys.stdout = fp
        gen()
