{-# Language ViewPatterns #-}

import Test.Tasty
import Test.Tasty.HUnit
import Math.MFSolve
import Data.List
import Data.Maybe

data TestExpr = TestExpr
                ((SimpleVar -> Double) -> Double)
                (Expr SimpleVar Double)

type TestEq = ((SimpleVar -> Double) -> String,
               (Expr SimpleVar Double,
                Expr SimpleVar Double))

testVar :: String -> TestExpr
testVar str = TestExpr ($ SimpleVar str) (makeVariable $ SimpleVar str)

testConst :: Double -> TestExpr
testConst n = TestExpr (const n) (makeConstant n)

testBin :: (Double -> Double -> Double)
        -> (Expr SimpleVar Double
            -> Expr SimpleVar Double -> Expr SimpleVar Double)
        -> TestExpr -> TestExpr -> TestExpr
testBin f f2(TestExpr a b) (TestExpr c d) =
  TestExpr (\s -> f (a s) (c s)) (f2 b d)

testUn :: (Double -> Double)
       -> (Expr SimpleVar Double -> Expr SimpleVar Double)
       -> TestExpr -> TestExpr
testUn f f2(TestExpr a b) =
  TestExpr (f.a) (f2 b)

testEq :: Double -> Double -> String -> String -> String
testEq a b as bs
  | abs(a-b) <= 1e-10 =
      ""
  | otherwise =
      "substituting solutions in:\n"
      ++ as ++ " = " ++ bs ++ "\n" ++
      "gives: " ++ show a ++ " = " ++ show b ++ "\n"

infixr 1 ?= 
(?=) :: TestExpr -> TestExpr -> TestEq

zero :: (Num n, Eq n) => Expr v n -> Bool
zero (toSimple -> Const 0) = True
zero _ = False

instance (Floating n, Eq n, Ord n, Ord v) => Eq (Expr v n) where
  a == b = zero $ a-b

TestExpr a b ?= TestExpr c d =
  (\s -> testEq (a s) (c s) (show b) (show d),
   (b,d))

instance Num TestExpr where
  (+) = testBin (+) (+)
  (*) = testBin (*) (*)
  signum = testUn signum signum
  abs = testUn abs abs
  fromInteger = testConst . fromInteger
  negate = testUn negate negate

instance Fractional TestExpr where
  recip = testUn recip recip
  fromRational = testConst . fromRational

instance Floating TestExpr where
  pi = testConst pi
  exp = testUn exp exp
  log = testUn log log
  sin = testUn sin sin 
  cos = testUn cos cos
  cosh = testUn cosh cosh
  atanh = testUn atanh atanh
  tan = testUn tan tan
  sinh = testUn sinh sinh
  asin = testUn asin asin
  acos = testUn acos acos
  asinh = testUn asinh asinh
  acosh = testUn acosh acosh
  atan = testUn atan atan

a, b, c, d, x, y :: TestExpr
[a, b, c, d, x, y] = map testVar ["a", "b", "c", "d", "x", "y"]

randomSol :: [(SimpleVar, Double)]
randomSol = [
  (SimpleVar "a", 0.897),
  (SimpleVar "b", 0.905),
  (SimpleVar "c", -0.585),
  (SimpleVar "d", 0.018),
  (SimpleVar "x", -0.3628),
  (SimpleVar "y", 0.887)]

trySolve :: [TestEq]  -> Assertion
trySolve eqs =
  assertString $ fromMaybe "" $
  find (not.null) $ map solveOne $
  permutations eqs

solveOne :: [TestEq] -> String
solveOne eqs =  
  case flip execSolver noDeps $
       mapM (uncurry (===) . snd) eqs
  of
   Left RedundantEq ->
     "Found redundant equation"
   Left (InconsistentEq n) ->
     "Equation off by "++ show n
   Right d
     | not $ null $ nonlinearEqs d ->
       "Some nonlinear equations were unevaluated:\n" ++
       show d
     | not $ null $ dependendVars d ->
       "Some linear dependencies were left:\n" ++
       show d
     | otherwise ->
       let kv = knownVars d ++ randomSol
           sols = map (($ (fromMaybe 0 . (`lookup` kv))).fst) eqs
       in case find (not.null) sols of
           Nothing -> ""
           Just er ->
             "Solution didn't match equations:\n" ++
             show d ++ er

sysHasVar :: (Ord t, Ord v, Floating t) => Dependencies v t -> v -> Bool
sysHasVar s v = 
  any ((== v).fst) (knownVars s) ||
  any (\(v2, LinExpr _ vs) ->
        v==v2 || any ((== v).fst) vs)
  (dependendVars s) ||
  any (hasVar v) (nonlinearEqs s)

{-

eliminate v from eqs
check number of eliminated equations
eqs2 = add v to eqs
check eqs and eqs2 for equality

-}


tryElim v n eqs =
  undefined

tests :: TestTree
tests = testGroup "Tests" [unitTests]

unitTests = testGroup "Unit tests" [
  testCase "Linear system of equations" $
  trySolve [
    3*a + 2*b - c ?= 1,
    2*a - 2*b + 4 ?= -2,
    -a + b/2 - c ?= 0],

  testCase "Solve single sine" $
  trySolve [
    2*sin(0.3*a - 2*b + pi/8) ?= -1.42,
    3*a+2*b ?= 7],

  testCase "Adding sinewaves with same period" $
  trySolve [
    a ?= 2*b,
    2*sin(a + 0.1) + 3*cos(2*b + 0.1) ?= -0.524],
    
  testCase "Adding sinewaves with same period (using substitution)" $
  trySolve [
    2*x + 3*y ?= -0.524,
    a ?= 2*b,
    x ?= sin(a + 0.1),
    y ?= cos(2*b + 0.1)],

  testCase "Solving for angle and amplitude" $
  trySolve [
    a*sin (b+c+0.1) ?= 5,
    a*cos (b+c+0.2) ?= 6,
    b+2*c ?= 3],

  testCase "Mixing nonlinear and trigonometric functions" $
  trySolve [
    sqrt a * (b + sin(2*c)) ?= 0.243,
    a - b ?= 1,
    a + b ?= 3],
  
  testCase "Simplifying nonlinear into trigonometric." $
  trySolve [
    2*sin(2*c*sqrt b) ?= a,
    a - b ?= 1,
    a + b ?= 3],

  testCase "Simplifying trigonometric into linear" $
  trySolve [
    sin(a+b*2) ?= c,
    2*a+4*b ?= pi/8,
    b ?= 2*c],

  testCase "Rotation by rotation matrix." $
  trySolve [
    cos a*x - sin a*y ?= 10,
    sin a*x + cos a*y ?= 13,
    x ?= d*sin b,
    y ?= d*cos b,
    b ?= pi/3
    ]
  ]

main = defaultMain tests
