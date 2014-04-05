MFSolve
=======

MFSolve is a haskell library for solving linear equations in an iterative way, like in metafont.

This allows variables to be used in nonlinear expressions, as long as
the value of the variable has been already reduced to a number.  A
numeric instance is provided so that the regular haskell functions can
be used on expressions involving variables.

For example:

```haskell
-- Turn the given strings into variables.
[a, b, c, d] = map makeVariable ["a", "b", "c", "d"]

test = showVars $ solveEq emptyDeps [
  a === 0.8*b + 0.2*c,
  d === pi/2,
  b+a === sin(d),
  c === d
]
```

returns:

```
"d" = 1.5707963267948966
"a" = 0.6189773696438774
"b" = 0.3810226303561226
"c" = 1.5707963267948966
```