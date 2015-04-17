MFSolve
=======

MFSolve is an equation solver that solves and evaluates
expressions on the fly.  It is based on Prof. D.E.Knuth's
_metafont_.  The goal of mfsolve is to make the solver useful in an
interactive program, by enhancing the bidirectionality of the solver.
Like metafont, it can solve linear equations, and evaluate nonlinear
expressions.  In addition to metafont, it also solves for angles, and
makes the solution independend of the order of the equations.

The `Expr` type allows for calculations with constants and unknown
variables.

Examples:
---------

Let's define some variables.  The `SimpleVar` type is a simple wrapper
around `String` to provide nice output.  The `Dependencies` datatype
contains all dependencies and known equations.

```haskell
let [x, y, t, a] = map (makeVariable . SimpleVar) ["x", "y", "t", "a"]
```
Solve linear equations:

```haskell
showVars $ solveEqs emptyDeps
[ 2*x + y === 5,
  x - y   === 1]
```

```
x = 2.0
y = 1.0
```

Solve for angle (pi/4):

```haskell
showVars $ solveEqs emptyDeps
[ sin(t) === 1/sqrt(2) ]
```

```
t = 0.7853981633974484
```

Solve for angle (pi/3) and amplitude:

```haskell
showVars $ solveEqs emptyDeps
[ a*sin(x) === sqrt 3,
  a*cos(x) === 1 ]
```

```
x = 1.0471975511965979
a = 2.0
```

Allow nonlinear expression with unknown variables:

```haskell
showVars $ solveEqs emptyDeps
[ sin(sqrt(x)) === y,
  x === 2]
```

```
x = 2.0
y = 0.9877659459927355
```

Find the angle and amplitude when using a rotation matrix:

```haskell
showVars $ solveEqs emptyDeps
[ a*cos t*x - a*sin t*y === 30,
  a*sin t*x + a*cos t*y === 40,
  x === 10,
  y === 10 ]
```

```
x = 10.0
y = 10.0
t = 0.14189705460416402
a = 3.5355339059327373
```
