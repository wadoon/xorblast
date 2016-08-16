#!/bin/bash

FILE=$1
OUT=$1.blast


../build/xorblastpp -s $FILE.smt2 -g -o $OUT $FILE

if [ $? -eq 42 ]; then
    echo "$FILE ... contradiction"
    exit 0
fi

./cnf2smt.py  $OUT $FILE > tmp.smt2


echo -n "$1 ... "

function z3test() {
    timeout 2m z3 -smt2 $FILE.smt2 | grep unsat &>/dev/null
    if [ ${PIPESTATUS[0]} -ge 127 ]; then
        return 127
    fi
    return ${PIPESTATUS[1]}
}

z3test
e=$?
if [ $e -eq 0 ]; then
    echo "ok"
    exit 0
elif [ $e -gt 123 ]; then
    echo "timeout"
    exit 0
else
    echo "bad $e"
    exit $e
fi
