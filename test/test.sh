#!/bin/bash

FILE=$1
OUT=$1.blast


../build/xorblastpp -v -g -o $OUT $FILE
./cnf2smt.py  $OUT $FILE > tmp.smt2


if z3 -smt2 tmp.smt2; then
    exit 1
else
    exit 0
fi
