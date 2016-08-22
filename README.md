[![Build Status](https://travis-ci.org/wadoon/xorblast.svg?branch=master)](https://travis-ci.org/wadoon/xorblast)

xorblast
==========

A CNF preprocessor for xor constraints.

* Author:   Alexander Weigl <weigl@kit.edu>
* License:  GPLv3



What does the prepocessor
==================================

`xorblast` reads dimacs files, which contains xor clauses of the form:

```
x <var1> <var2> <var3> <var4> 0
x -<var5> <var6> <var7> 0
```

where the first line represents the formula: `var1 ^ var2 ^ var3 ^ var4`.
and the second line represents the formula: `not (var5 ^ var6 ^ var7)`.
Just think on odd or even bit parity.

`xorblast` catches these constraints, simplifies them by Gauss-Jordan
elimination in GF(2) and expands the residual xor clauses with Tseitin encoding.

**Take care**, that Tseitin encoded is only satisfiable equivalent. So the new
CNF formula is satisfiable if the given CNF formula is satisfiable. For example,
the new CNF formula have more models.

Getting Started
====================

Install the development files  `m4ri` library. On debian: `libm4ri-dev`, on fedora systems: `libm4ri-devel`.

```
$ git clone https://github.com/wadoon/xorblast.git
$ cd xorblast && mkdir build && cd build && cmake .. && make
```

Currently following switches are supported:

* `-g/-G` enables and disable the gauss elimination
* `-v` verbose (debug) output
* `-s FILE` writes SMT to `FILE` with a proof obligation of equality of the
  gauss elimination
