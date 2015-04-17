{-# LANGUAGE DeriveGeneric, PatternGuards, ViewPatterns #-}

{-|
Module      : Math.MFSolve
Description : Equation solver and calculator à la metafont
Copyright   : (c) Kristof Bastiaensen, 2015
License     : BSD-3
Maintainer  : kristof@resonata.be
Stability   : unstable
Portability : portable

This module implements an equation solver that solves and evaluates
expressions on the fly.  It is based on Prof. D.E.Knuth's
/metafont/.  The goal of mfsolve is to make the solver useful in an
interactive program, by enhancing the bidirectionality of the solver.
Like metafont, it can solve linear equations, and evaluate nonlinear
expressions.  In addition to metafont, it also solves for angles, and
makes the solution independend of the order of the equations.

The `Expr` datatype allows for calculations with constants and unknown
variables.  The `Dependencies` datatype contains all dependencies and known equations.

=== Examples:

Let's define some variables.  The `SimpleVar` type is a simple wrapper
around `String` to provide nice output.

> let [x, y, t, a] = map (makeVariable . SimpleVar) ["x", "y", "t", "a"]

Solve linear equations:

> showVars $ solveEqs emptyDeps
> [ 2*x + y === 5,
>   x - y   === 1]

> x = 2.0
> y = 1.0

Solve for angle (pi/4):

> showVars $ solveEqs emptyDeps
> [ sin(t) === 1/sqrt(2) ]

> t = 0.7853981633974484

Solve for angle (pi/3) and amplitude:

> showVars $ solveEqs emptyDeps
> [ a*sin(x) === sqrt 3,
>   a*cos(x) === 1 ]

> x = 1.0471975511965979
> a = 2.0

Allow nonlinear expression with unknown variables:

> showVars $ solveEqs emptyDeps
> [ sin(sqrt(x)) === y,
>   x === 2]

>x = 2.0
>y = 0.9877659459927355

Find the angle and amplitude when using a rotation matrix:

> showVars $ solveEqs emptyDeps
> [ a*cos t*x - a*sin t*y === 30,
>   a*sin t*x + a*cos t*y === 40,
>   x === 10,
>   y === 10 ]

> x = 10.0
> y = 10.0
> t = 0.14189705460416402
> a = 3.5355339059327373

-}

module Math.MFSolve
       (SimpleExpr(..), Expr, LinExpr(..), UnaryOp(..), BinaryOp(..),
        Dependencies, DepError(..), SimpleVar(..),
        getKnown, knownVars, varDefined, nonlinearEqs, dependendVars,
        simpleExpr, emptyDeps, makeVariable, makeConstant,
        (===), (=&=), solveEqs, showVars)
where
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as H
import GHC.Generics
import Data.Hashable
import Data.Maybe
import Data.List
import Data.Function(on)
import Control.Monad

infixr 1 === , =&=

--  | _labeled_ black box mathematical functions
data UnaryFun n = UnaryFun UnaryOp (n -> n)

data BinaryOp = Add | Mul
              deriving Eq
data UnaryOp =
  Sin | Abs | Recip | Signum |
  Exp | Log | Cos | Cosh | Atanh |
  Tan | Sinh | Asin | Acos | Asinh | Acosh | Atan
  deriving (Eq, Generic)

-- | A simplified datatype representing an expression
data SimpleExpr v n =
  SEBin BinaryOp (SimpleExpr v n) (SimpleExpr v n) |
  SEUn UnaryOp (SimpleExpr v n) |
  Var v |
  Const n

newtype SimpleVar = SimpleVar String
                  deriving (Eq, Ord, Generic)

-- | An mathematical expression of several variables.
data Expr v n = Expr (LinExpr v n) [TrigTerm v n] [NonLinExpr v n]
                deriving Generic

-- | A linear expression of several variables.
-- For example: @2*a + 3*b + 2@ would be represented as
-- @LinExpr 2 [(a, 2), (b, 3)]@.
data LinExpr v n = LinExpr n [(v, n)]
                 deriving (Generic, Eq, Show)
type Period v n = [(v, n)]
type Phase n = n
type Amplitude v n = LinExpr v n

-- A sum of sinewaves with the same period (a linear sum of several
-- variables), but possibly different (constant) phase.  For example
-- @(2*a+b) sin (x+y) + 2*b*sin(x+y+pi)@ would be represented by:
-- @TrigTerm [(x,1),(y,1)] [(0, LinExpr 0 [(a, 2), (b, 1)]),
-- (pi, LinExpr 0 [(b, 2)])@
type TrigTerm v n = (Period v n, [(Phase n, Amplitude v n)])

-- Any other term
data NonLinExpr v n = 
  UnaryApp (UnaryFun n) (Expr v n) |
  MulExp (Expr v n) (Expr v n) |
  SinExp (Expr v n)
  deriving Generic

-- | An angular function of the form @c + n*sin(theta + alpha)@
-- where @theta@, and @n@ are linear terms, @alpha@ and @c@ are constants.
type LinearMap v n = M.HashMap v (LinExpr v n)
type TrigEq v n = (Period v n, Amplitude v n, Phase n, n)
type TrigEq2 v n = M.HashMap (Period v n)
                   (M.HashMap v (Expr v n))

instance (Hashable v, Hashable n) => Hashable (LinExpr v n)
instance (Hashable v, Hashable n) => Hashable (NonLinExpr v n)
instance (Hashable n) => Hashable (UnaryFun n) where
  hashWithSalt s (UnaryFun o _) = hashWithSalt s o
instance Hashable UnaryOp
instance (Hashable v, Hashable n) => Hashable (Expr v n)
instance Hashable SimpleVar

-- | A simple String wrapper, which will print formulas more cleanly.
instance Show SimpleVar where
  show (SimpleVar s) = s

-- | An opaque datatype containing the dependencies of each variable.
-- A variable who's dependency is just a number is called /known/.  A
-- variables which depends on other variables is called /dependend/.
-- A variable which is neither known or dependend is called
-- /independend/.  A variable can only depend on other /independend/
-- variables.  It also contains nonlinear equations which it couldn't
-- reduce to a linear equation yet.
data Dependencies v n = Dependencies
                        (M.HashMap v (H.HashSet v))
                        (LinearMap v n)
                        [TrigEq v n]
                        (TrigEq2 v n)
                        [Expr v n]
                        
-- | An error type for '===', '=&=' and 'solveEq':
data DepError n =
  -- | 'InconsistentEq' @a@: The equation was reduced to the
  -- impossible equation `a == 0` for nonzero a, which means the
  -- equation is inconsistent with previous equations.
  InconsistentEq n |
  -- | 'RedundantEq': The equation was reduced to the redundant equation 0 == 0, which
  -- means it doesn't add any information.
  RedundantEq

instance (Ord n, Num n, Eq n, Show v, Show n) => Show (Expr v n) where
  show e = show (simpleExpr e)

withParens :: (Show t1, Show t, Ord t1, Num t1, Eq t1) => SimpleExpr t t1 -> [BinaryOp] -> String
withParens e@(SEBin op _ _) ops
  | op `elem` ops = "(" ++ show e ++ ")"
withParens e _ = show e

instance (Show v, Ord n, Show n, Num n, Eq n) => Show (SimpleExpr v n) where
  show (Var v) = show v
  show (Const n) = show n
  show (SEBin Add e1 (SEBin Mul (Const e2) e3))
    | e2 < 0 =
      show e1 ++ " - " ++ show (SEBin Mul (Const (negate e2)) e3)
  show (SEBin Add e1 e2) =
    show e1 ++ " + " ++ show e2
  show (SEBin Mul (Const 1) e) = show e
  show (SEBin Mul e (Const 1)) = show e
  show (SEBin Mul e1 (SEUn Recip e2)) =
    withParens e1 [Add] ++ "/" ++ withParens e2 [Add, Mul]
  show (SEBin Mul e1 e2) =
    withParens e1 [Add] ++ "*" ++ withParens e2 [Add]
  show (SEUn Exp (SEBin Mul (SEUn Log e1) e2)) =
    withParens e1 [Add, Mul] ++ "**" ++ withParens e2 [Add, Mul]
  show (SEUn op e) = show op ++ "(" ++ show e ++ ")"

instance Show BinaryOp where
  show Add = "+"
  show Mul = "*"

instance Show UnaryOp where
  show Sin = "sin"
  show Abs = "abs"
  show Recip = "1/"
  show Signum = "sign"
  show Exp = "exp"
  show Log = "log"
  show Cos = "cos"
  show Cosh = "cosh"
  show Atanh = "atanh"
  show Tan = "tan"
  show Sinh = "sinh"
  show Asin = "asin"
  show Acos = "acos"
  show Asinh = "asinh"
  show Acosh = "acosh"
  show Atan = "atan"

instance (Floating n, Ord n, Ord v) => Num (Expr v n) where
  (+) = addExpr
  (*) = mulExpr
  negate = mulExpr (makeConstant (-1))
  abs = unExpr (UnaryFun Abs abs)
  signum = unExpr (UnaryFun Signum signum)
  fromInteger = makeConstant . fromInteger

instance (Floating n, Ord n, Ord v) => Fractional (Expr v n) where
  recip = unExpr (UnaryFun Recip (1.0/))
  fromRational = makeConstant . fromRational

instance (Floating n, Ord n, Ord v) => Floating (Expr v n) where
  pi = makeConstant pi
  exp = unExpr (UnaryFun Exp exp)
  log = unExpr (UnaryFun Log log)
  sin = sinExpr
  cos a = sinExpr (a + makeConstant (pi/2))
  cosh = unExpr (UnaryFun Cosh cosh)
  atanh = unExpr (UnaryFun Atanh atanh)
  tan = unExpr (UnaryFun Tan tan)
  sinh = unExpr (UnaryFun Sinh sinh)
  asin = unExpr (UnaryFun Asin asin)
  acos = unExpr (UnaryFun Acos acos)
  asinh = unExpr (UnaryFun Asinh asinh)
  acosh = unExpr (UnaryFun Acosh acosh)
  atan = unExpr (UnaryFun Atan atan)

instance (Show n, Floating n, Ord n, Ord v, Show v) =>Show (Dependencies v n) where
  show dep@(Dependencies _ lin _ _ _) = 
    unlines (map showLin (M.toList lin) ++
             map showNl (nonlinearEqs dep))
    where showLin (v, e) = show v ++ " = " ++ show (linExpr e)
          showNl e = show e ++ " = 0"

instance (Show n) => Show (DepError n) where
  show (InconsistentEq a) =
    "Inconsistent equations, off by " ++ show a
  show RedundantEq =
    "Redundant Equation."


addSimple :: (Num t1, Eq t1) => SimpleExpr t t1 -> SimpleExpr t t1 -> SimpleExpr t t1
addSimple (Const 0) e = e
addSimple e (Const 0) = e
addSimple e1 e2 = SEBin Add e1 e2

linToSimple :: (Num t1, Eq t1) => LinExpr t t1 -> SimpleExpr t t1
linToSimple (LinExpr v t) =
  Const v `addSimple`
  foldr (addSimple.mul) (Const 0) t
  where
    mul (v2, 1) = Var v2
    mul (v2, c) = SEBin Mul (Const c) (Var v2)
    
trigToSimple :: (Num n, Eq n) => TrigTerm v n -> SimpleExpr v n
trigToSimple (theta, t) =
  foldr (addSimple.makeSin) (Const 0) t
  where
    makeSin (alpha, n) =
      SEBin Mul (linToSimple n)
      (SEUn Sin angle) where
        angle | alpha == 0 =
                linToSimple (LinExpr 0 theta)
              | otherwise =
                SEBin Add (linToSimple (LinExpr 0 theta))
                (Const alpha)

nonlinToSimple :: (Num n, Eq n) => NonLinExpr v n -> SimpleExpr v n
nonlinToSimple (UnaryApp (UnaryFun o _) e) =
  SEUn o (simpleExpr e)
nonlinToSimple (MulExp e1 e2) =
  SEBin Mul (simpleExpr e1) (simpleExpr e2)
nonlinToSimple (SinExp e) =
  SEUn Sin (simpleExpr e)

-- | Convert an `Expr` to a `SimpleExpr`.
simpleExpr :: (Num n, Eq n) => Expr v n -> SimpleExpr v n
simpleExpr (Expr lin trig nonlin) =
  linToSimple lin `addSimple`
  foldr (addSimple.trigToSimple)
  (Const 0) trig `addSimple`
  foldr (addSimple.nonlinToSimple)
  (Const 0) nonlin

zeroTerm :: (Num n) => LinExpr v n
zeroTerm = LinExpr 0 []

linExpr :: LinExpr v n -> Expr v n
linExpr lt = Expr lt [] []

-- | Create an expression from a constant
makeConstant :: n -> Expr v n
makeConstant c = linExpr (LinExpr c [])

-- | Create an expression from a variable
makeVariable :: Num n => v -> Expr v n
makeVariable v = linExpr (LinExpr 0 [(v, 1)])

trigExpr :: (Num n) => [TrigTerm v n] -> Expr v n
trigExpr t = Expr zeroTerm t []

nonlinExpr :: Num n => [NonLinExpr v n] -> Expr v n
nonlinExpr = Expr zeroTerm []

getConst :: LinExpr t a -> Maybe a
getConst (LinExpr a []) = Just a
getConst _ = Nothing

getLin :: Expr t n -> Maybe (LinExpr t n)
getLin (Expr lt [] []) = Just lt
getLin _ = Nothing

getConstExpr :: Expr t b -> Maybe b
getConstExpr e = getLin e >>= getConst

addLin :: (Ord v, Num n, Eq n) => LinExpr v n -> LinExpr v n -> LinExpr v n
addLin (LinExpr c1 terms1) (LinExpr c2 terms2) =
  LinExpr (c1+c2) terms3 where
    terms3 = filter ((/= 0) . snd) $
             merge terms1 terms2 (+)

addExpr :: (Ord n, Ord v, Floating n) => Expr v n -> Expr v n -> Expr v n
addExpr (Expr lt1 trig1 nl1) (Expr lt2 trig2 nl2) =
  Expr (addLin lt1 lt2) trig3 (nl1++nl2)
  where
    trig3 = merge trig1 trig2 addTrigTerms

-- merge two association lists, by combining equal keys with
-- the given function, and keeping keys sorted.
merge :: Ord k => [(k, v)] -> [(k, v)] -> (v -> v -> v) -> [(k, v)]
merge [] l _ = l
merge l [] _ = l
merge (a@(k,v):as) (b@(k2,v2):bs) f = case compare k k2 of
  LT -> a: merge as (b:bs) f
  EQ -> (k, f v v2): merge as bs f
  GT -> b: merge (a:as) bs f

-- add trigonometric terms with the same period
addTrigTerms :: (Ord a, Ord t, Floating a) => [(a, LinExpr t a)] -> [(a, LinExpr t a)] -> [(a, LinExpr t a)]
addTrigTerms [] p = p
addTrigTerms terms terms2 =
  foldr mergeTerms terms terms2
  where
    mergeTerms (alpha, n) ((beta, m):rest) =
      case addTrigTerm alpha n beta m of
       Just (_, LinExpr 0 []) -> rest
       Just (gamma, o) ->
         mergeTerms (gamma, o) rest
       Nothing -> (beta, m) : mergeTerms (alpha, n) rest
    mergeTerms a [] = [a]

addTrigTerm :: (Ord a, Ord t, Floating a) => a -> LinExpr t a -> a -> LinExpr t a -> Maybe (a, LinExpr t a)
addTrigTerm alpha n beta m
  | alpha == beta =
    Just (alpha, addLin n m)
  | Just r <- termIsMultiple n m =
      let gamma = atan (divident/divisor) +
                  (if divisor < 0 then pi else 0)
          divident = r*sin alpha + sin beta
          divisor = r*cos alpha + cos beta
          o = sqrt(divident*divident + divisor*divisor)
      in Just (gamma, mulLinExpr o m)
  | otherwise = Nothing

-- compare if the linear term is a multiple of the other, within roundoff                
termIsMultiple :: (Ord a, Fractional a, Eq t) => LinExpr t a -> LinExpr t a -> Maybe a
termIsMultiple (LinExpr _ _) (LinExpr 0 []) = Nothing
termIsMultiple (LinExpr 0 []) (LinExpr _ _) = Nothing
termIsMultiple (LinExpr 0 r1@((_, d1):_)) (LinExpr 0 r2@((_, d2):_))
  | compareBy r1 r2 (compareTerm (d1/d2)) =
      Just (d1/d2)
termIsMultiple (LinExpr c1 r1) (LinExpr c2 r2)
  | compareBy r1 r2 (compareTerm (c1/c2)) =
      Just (c1/c2)
  | otherwise = Nothing

compareTerm :: (Ord a1, Fractional a1, Eq a) => a1 -> (a, a1) -> (a, a1) -> Bool
compareTerm ratio (v3,c3) (v4, c4) = 
  v3 == v4 && (abs(c3 - (c4 * ratio)) <= abs c3*2e-50)

compareBy :: [a] -> [b] -> (a -> b -> Bool) -> Bool
compareBy [] [] _ = True
compareBy (e:l) (e2:l2) f =
  f e e2 && compareBy l l2 f
compareBy _ _ _ = False
        
-- multiply a linear term by a constant.
mulLinExpr :: Num n => n -> LinExpr v n -> LinExpr v n
mulLinExpr x (LinExpr e terms) =
  LinExpr (e*x) $ map (fmap (*x)) terms

-- multiply all sines with the constant
-- constant multiplier
mulConstTrig :: (Ord n, Num n) => n -> TrigTerm v n -> TrigTerm v n
mulConstTrig c (theta, terms) =  (theta, tt) where
  tt = map (fmap (mulLinExpr c)) terms

mulLinTrig :: (Ord n, Ord v, Floating n) => LinExpr v n -> TrigTerm v n -> Expr v n
mulLinTrig lt (theta, terms) =
  -- linear multiplier
  foldr ((+).mul1) 0 terms
  where
    -- constant amplitude
    mul1 (alpha, LinExpr c []) =
      trigExpr [(theta, [(alpha, mulLinExpr c lt)])]
    -- linear amplitude
    mul1 t =
      nonlinExpr [MulExp (trigExpr [(theta, [t])])
                      (Expr lt [] [])]

-- constant * (linear + trig)
mulExpr :: (Ord a, Ord t, Floating a) => Expr t a -> Expr t a -> Expr t a
mulExpr (getConstExpr -> Just c) (Expr lt2 trig []) =
  Expr (mulLinExpr c lt2)
  (map (mulConstTrig c) trig) []

mulExpr (Expr lt2 trig []) (getConstExpr -> Just c) =
  Expr (mulLinExpr c lt2)
  (map (mulConstTrig c) trig) []

-- linear * (constant + trig)
mulExpr (getLin -> Just lt) (Expr (getConst -> Just c) trig []) =
  linExpr (mulLinExpr c lt) +
  foldr ((+).mulLinTrig lt) 0 trig

mulExpr (Expr (getConst -> Just c) trig []) (getLin -> Just lt) =
  linExpr (mulLinExpr c lt) +
  foldr ((+).mulLinTrig lt) 0 trig

-- anything else
mulExpr e1 e2 = nonlinExpr [MulExp e1 e2]
      
sinExpr :: Floating n => Expr v n -> Expr v n
sinExpr (Expr (LinExpr c t) [] [])
  | null t = makeConstant (sin c)
  | otherwise = trigExpr [(t, [(c, LinExpr 1 [])])]
sinExpr e = nonlinExpr [SinExp e]

unExpr :: Num n => UnaryFun n -> Expr v n -> Expr v n
unExpr (UnaryFun _ f) e
  | Just c <- getConstExpr e = makeConstant (f c)
unExpr f e = nonlinExpr [UnaryApp f e]

substVarLin :: (Ord v, Num n, Eq n) => (v -> Maybe (LinExpr v n)) -> LinExpr v n -> LinExpr v n
substVarLin s (LinExpr a terms) =
  let substOne (v, c) =
        maybe (LinExpr 0 [(v, c)]) (mulLinExpr c) (s v)
  in foldr (addLin.substOne) (LinExpr a []) terms

substVarNonLin :: (Ord n, Ord v, Floating n) => (v -> Maybe (LinExpr v n)) -> NonLinExpr v n -> Expr v n
substVarNonLin s (UnaryApp f e1) =
  unExpr f (subst s e1)
substVarNonLin s (MulExp e1 e2) =
  subst s e1 * subst s e2
substVarNonLin s (SinExp e1) =
  sin (subst s e1)

substVarTrig :: (Ord v, Ord n, Floating n) => (v -> Maybe (LinExpr v n)) -> ([(v, n)], [(n, LinExpr v n)]) -> Expr v n
substVarTrig s (period, terms) =
  let period2 = linExpr $ substVarLin s (LinExpr 0 period)
      terms2 = map (fmap $ linExpr.substVarLin s) terms
  in foldr (\(p,a) -> (+ (a * sin (makeConstant p + period2))))
     0 terms2

subst :: (Ord n, Ord v, Floating n) => (v -> Maybe (LinExpr v n)) -> Expr v n -> Expr v n
subst s (Expr lt trig nl) =
  linExpr (substVarLin s lt) +
  foldr ((+).substVarTrig s) 0 trig +
  foldr ((+).substVarNonLin s) 0 nl

-- | An empty set of dependencies.
emptyDeps :: Dependencies v n
emptyDeps = Dependencies M.empty M.empty [] M.empty []

simpleSubst :: Eq a => a -> b -> a -> Maybe b
simpleSubst x y z
  | x == z = Just y
  | otherwise = Nothing

-- | Make the expressions on both sides equal, and add the result to the Set of
-- dependencies.
(===) :: (Hashable n, Hashable v, RealFrac (Phase n), Ord v,
          Floating n) => Expr v n -> Expr v n
         -> Dependencies v n
         -> Either (DepError n) (Dependencies v n)
(===) lhs rhs deps = addEq deps (lhs - rhs)

addEqs :: (Hashable v, Hashable n, RealFrac (Phase n), Ord v, Floating n) => Dependencies v n -> [Expr v n] -> Either (DepError n) (Dependencies v n)
addEqs = foldM addEq

addEq :: (Hashable n, Hashable v, RealFrac (Phase n), Ord v,
          Floating n) =>
         Dependencies v n
         -> Expr v n -> Either (DepError n) (Dependencies v n)
addEq deps@(Dependencies _ lin _ _ _) expr =
  addEq0 deps $
  -- substitute known and dependend variables
  subst (flip M.lookup lin) expr
  
-- the following alternative would continue after a redundant error.
-- However a redundant expression is supposed to be an error in metafont.
-- 
-- addEqs dep [] = Right dep
-- addEqs dep (e:r) =
--   case addEq0 dep e of
--    Left (InconsistentEq c) ->
--      Left $ InconsistentEq c
--    Left RedundantEq ->
--      addEqs dep r
--    Right newdep ->
--      case addEqs newdep r of
--       Left (InconsistentEq c) ->
--         Left $ InconsistentEq c
--       Left RedundantEq -> Right newdep
--       Right newerdep -> Right newerdep

-- This one is by Cale Gibbard: 

select :: [a] -> [(a, [a])]
select [] = []
select (x:xs) =
  (x,xs) : [(y,x:ys) | (y,ys) <- select xs]
  
addEq0 :: (Hashable v, Hashable n, RealFrac (Phase n), Ord v, Floating n) => Dependencies v n -> Expr v n -> Either (DepError n) (Dependencies v n)
-- adding a constant equation
addEq0 _  (getConstExpr -> Just c) =
  if c == 0 then Left RedundantEq
  else Left (InconsistentEq c)

-- adding a linear equation
addEq0 (Dependencies vdep lin trig trig2 nonlin) (Expr lt [] []) =
  let (v, _, lt2) = splitMax lt
      -- variables that depend on v
      depVars = fromMaybe H.empty (M.lookup v vdep)
      -- substitute v in all dependend variables
      -- and add v as dependend variable
      lin' = M.insert v lt2 $
             H.foldl' (flip $ M.adjust $ substVarLin $
                       simpleSubst v lt2) lin depVars
      -- independend variables substituted
      ltVars = case lt2 of
        LinExpr _ vars -> map fst vars
      -- add dependency link from independend variables to the
      -- substituted equations and v, and remove v (since it has
      -- become dependend, so no variable can depend on it).
      depVars2 = H.insert v depVars
      vdep' = H.foldl'
              (\mp k -> M.insertWith H.union k depVars2 mp)
              (M.delete v vdep) (H.fromList ltVars)
      -- simply substitute var in nonlinear eqs
      nonlin' = map (subst (simpleSubst v lt2)) nonlin
      -- substitute and evaluate trigonometric equations
      trigSubst (p, a, ph, c) =
        subst (simpleSubst v lt2) $
        sin (linExpr $ LinExpr ph p) *
        linExpr a + makeConstant c
      newTrig = map trigSubst trig
      trigSubst2 (v2, ex) =
        subst (simpleSubst v lt2) $
        makeVariable v2 - ex
      newTrig2 =
        map trigSubst2 $
        concatMap M.toList $
        M.elems trig2
      
  in addEqs (Dependencies vdep' lin' [] M.empty []) (newTrig++newTrig2++nonlin')

-- adding a sine equation
addEq0 deps@(Dependencies vdep lin trig trig2 nl)
  (Expr (LinExpr c lt) [(theta, [(alpha, getConst -> Just n)])] []) =
  if null lt then
    -- reduce a sine to linear equation
    addEq0 deps (linExpr $ LinExpr (alpha - asin (-c/n)) theta)
  else
    -- add a variable dependency on the sine equation
    case M.lookup theta trig2 of
     -- no sine with same period
     Nothing -> addSin (LinExpr c lt) alpha n
     Just map2 ->
       case foldr ((+).doSubst)
            (makeConstant c +
             makeConstant n *
             sin (linExpr $ LinExpr alpha theta))
            lt of
        Expr lt2 [(_, [(alpha2, getConst -> Just n2)])] []
          | isNothing(getConst lt2)
          -> addSin lt2 alpha2 n2
        e2 -> addEq0 deps e2
       where
         doSubst (v,c2) = case M.lookup v map2 of
           Nothing -> makeVariable v * makeConstant c2
           Just e2 -> e2 * makeConstant c2
  where
    addSin l' a' n' =
      let (v, c', r) = splitMax l'
          trig2' = M.insertWith M.union theta
                   (M.singleton v $
                    Expr r [(theta, [(a', LinExpr (n'/negate c') [])])] [])
                   trig2
      in Right $ Dependencies  vdep lin trig trig2' nl

--  adding the first sine equation
addEq0 (Dependencies d lin [] trig2 nl) (Expr (getConst -> Just c) [(theta, [(alpha, n)])] []) =
  Right $ Dependencies d lin [(theta, n, alpha, c)] trig2 nl

-- try reducing this equation with another sine equation
addEq0 (Dependencies deps lin trig trig2 nl)
  (Expr (getConst -> Just x) [(theta, [(a, n)])] []) =
  case mapMaybe similarTrig $ select trig of
   -- no matching equation found
   [] -> Right $ Dependencies deps lin ((theta, n, a, x):trig) trig2 nl
   -- solve for angle and amplitude, and add resulting linear
   -- equations
   l -> addEqs (Dependencies deps lin rest trig2 nl) [lin1, lin2]
     where
       ((b,y), rest) = maximumBy (maxTrig `on` fst) l
       maxTrig (t1,_) (t2,_) = 
         compare ((t1-a)`dmod`pi) ((t2-a)`dmod`pi)
       d      = sin(a-b)
       e      = y*cos(a-b)-x
       theta2 = atan (-y*d/e)-b +
                (if (d*e) < 0 then pi else 0)
       n2     = sqrt(y*y + e*e/(d*d))
       lin1   = linExpr $ LinExpr (-theta2) theta
       lin2   = linExpr n - makeConstant n2
  where
    similarTrig ((t,m,b,y),rest)
      | Just r <- termIsMultiple m n,
        t == theta &&
        (b-a) `dmod` pi > pi/8 =
          Just ((b,y/r),rest)
      | otherwise = Nothing

-- just add any other equation to the list of nonlinear equations
addEq0 (Dependencies d lin trig trig2 nonlin) e =
  Right $ Dependencies d lin trig trig2 (e:nonlin)

dmod :: RealFrac a => a -> a -> a
dmod a b = abs((a/b) - fromInteger (round (a/b)) * b)

-- put the variable with the maximum coefficient on the lhs of the
-- equation
splitMax :: (Ord b, Fractional b, Eq v) => LinExpr v b -> (v, b, LinExpr v b)
splitMax (LinExpr c t) =
  let (v,c2) = maximumBy (compare `on` (abs.snd)) t
  in (v, c2,
      LinExpr (-c/c2) $
      map (fmap (negate.(/c2))) $
      filter ((/= v).fst) t)
      
-- | Return True if the variable is known or dependend.
varDefined :: (Eq v, Hashable v) => Dependencies v n -> v -> Bool
varDefined (Dependencies _ dep _ _ _) v =
  case M.lookup v dep of
    Nothing -> False
    _ -> True

-- | Return all dependend variables with their dependencies.
dependendVars :: (Eq n) => Dependencies v n -> [(v, LinExpr v n)]
dependendVars (Dependencies _ lin _ _ _) =
  filter (notConst.snd) (M.toList lin)
  where
    notConst (LinExpr _ []) = False
    notConst _ = True
  

-- | Return all known variables.
knownVars :: Dependencies v n -> [(v, n)]
knownVars (Dependencies _ lin _ _ _) =
  mapMaybe knownVar $ M.toList lin
  where
    knownVar (v, LinExpr n []) = Just (v, n)
    knownVar _ = Nothing

-- -- | Return all independend variables.
-- freeVars :: (Eq v, Hashable v) => Dependencies n v -> [v]
-- freeVars (Dependencies dep) =
--   HS.toList $ M.foldl' addVars HS.empty dep
--   where addVars s (LinExpr _ a) =
--           HS.union s $ HS.fromList $ map fst a

-- | Return the value of the variable, or a list of variables
-- it depends on.  Only linear dependencies are shown.
getKnown :: (Eq v, Hashable v) => Dependencies v n -> v -> Either [v] n
getKnown (Dependencies _ lin _ _ _) var =
  case M.lookup var lin of
    Nothing -> Left  []
    Just (LinExpr a []) ->
      Right a
    Just (LinExpr _ v) ->
      Left $ map fst v

trigToExpr :: (Ord n, Ord v, Floating n) => TrigEq v n -> Expr v n
trigToExpr (p, a, ph, c) =
  linExpr a * sin(linExpr $ LinExpr ph p) +
  makeConstant c

-- | Give all nonlinear equations as an `Expr` equal to 0.
nonlinearEqs :: (Ord n, Ord v, Floating n) => Dependencies v n -> [Expr v n]
nonlinearEqs  (Dependencies _ _ trig trig2 nl) =
  map trigToExpr trig ++
  map (\(v, e) -> makeVariable v - e) 
  (concatMap M.toList (M.elems trig2)) ++
  nl
  
-- | Make the pairs of expressions on both sides equal, and add the
-- result to the Set of dependencies.  No error is signaled if the
-- equation for one of the sides is redundant for example in (x, 0) ==
-- (y, 0).
(=&=) :: (Hashable n, Hashable v, RealFrac (Phase n), Ord v, Floating n) => (Expr v n, Expr v n) -> (Expr v n, Expr v n) -> Dependencies v n -> Either (DepError n) (Dependencies v n)
(=&=) (a, b) (c, d) dep = 
  case (a === c) dep of
    Left RedundantEq ->
      (b === d) dep
    Right res ->
      case (b === d) res of
        Left RedundantEq -> Right res
        Right res2 -> Right res2
        err -> err
    err -> err

-- | Solve a list of equations in order.  Returns either a new set of
-- dependencies, or signals an error.
solveEqs :: Dependencies v n -> [Dependencies v n -> Either (DepError n) (Dependencies v n)] -> Either (DepError n) (Dependencies v n)
solveEqs = foldM $ flip ($)

-- | Show all variables and equations.
showVars :: (Show n, Show v, Show a, Ord n, Ord v, Floating n) => Either (DepError a) (Dependencies v n) -> IO ()
showVars (Left e) = print e
showVars (Right dep) = print dep
