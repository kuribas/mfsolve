{-# LANGUAGE DeriveGeneric, PatternGuards, PatternSynonyms, MultiParamTypeClasses, FlexibleContexts, DeriveDataTypeable, GeneralizedNewtypeDeriving #-}

{-|
Module      : Math.MFSolve
Description : Equation solver and calculator à la metafont
Copyright   : (c) Kristof Bastiaensen, 2015
License     : BSD-3
Maintainer  : kristof@resonata.be
Stability   : unstable
Portability : ghc

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
around `String` to provide nice output, since the Show instance for
`String` outputs quotation marks.

> let [x, y, t, a] = map (makeVariable . SimpleVar) ["x", "y", "t", "a"]

Solve linear equations:

> showVars $ flip execSolver noDeps $ do
>   2*x + y === 5
>   x - y   === 1

> x = 2.0
> y = 1.0

Solve for angle (pi/4):

> showVars $ flip execSolver noDeps $ sin(t) === 1/sqrt(2)

> t = 0.7853981633974484

Solve for angle (pi/3) and amplitude:

> showVars $ flip execSolver noDeps $ do
>   a*sin(x) === sqrt 3
>   a*cos(x) === 1

> x = 1.0471975511965979
> a = 2.0

Allow nonlinear expression with unknown variables:

> showVars $ flip execSolver noDeps $ do
>   sin(sqrt(x)) === y
>   x === 2

>x = 2.0
>y = 0.9877659459927355

Find the angle and amplitude when using a rotation matrix:

> showVars $ flip execSolver noDeps $ do
>   a*cos t*x - a*sin t*y === 30
>   a*sin t*x + a*cos t*y === 40
>   x === 10
>   y === 10

> x = 10.0
> y = 10.0
> t = 0.14189705460416402
> a = 3.5355339059327373

-}

module Math.MFSolve
       (-- * Expressions
        SimpleExpr(..), Expr, LinExpr(..), UnaryOp(..), BinaryOp(..),
        SimpleVar(..),
        makeVariable,
        makeConstant, evalExpr, fromSimple, toSimple, evalSimple, hasVar, 
        -- * Dependencies
        Dependencies, DepError(..), 
        noDeps, addEquation, eliminate,
        getKnown, knownVars, varDefined, nonlinearEqs, dependendVars,
        -- * Monadic Interface
        (===), (=&=), dependencies, getValue, getKnownM,
        varDefinedM, eliminateM, ignore,
        -- * MFSolver monad
        MFSolver, 
        runSolver, evalSolver, execSolver, unsafeSolve, showVars,
        -- * MFSolverT monad transformer
        MFSolverT, 
        runSolverT, evalSolverT, execSolverT, unsafeSolveT)
where
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as H
import GHC.Generics
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.RWS
import Control.Monad.Cont
import Control.Exception
import Data.Typeable
import Control.Applicative hiding (Const)
import Data.Hashable
import Data.Maybe
import Data.List
import Data.Function(on)

data BinaryOp = Add | Mul
              deriving Eq
data UnaryOp =
  Sin | Abs | Recip | Signum |
  Exp | Log | Cos | Cosh | Atanh |
  Tan | Sinh | Asin | Acos | Asinh | Acosh | Atan
  deriving (Eq, Generic)

-- | A simplified datatype representing an expression.  This can be
-- used to inspect the structure of a `Expr`, which is hidden.
data SimpleExpr v n =
  SEBin BinaryOp (SimpleExpr v n) (SimpleExpr v n) |
  SEUn UnaryOp (SimpleExpr v n) |
  Var v |
  Const n

newtype SimpleVar = SimpleVar String
                  deriving (Eq, Ord, Generic)

-- | A mathematical expression of several variables. Several Numeric
-- instances (`Num`, `Floating` and `Fractional`) are provided, so
-- doing calculations over `Expr` is more convenient.
data Expr v n = Expr (LinExpr v n) [TrigTerm v n] [NonLinExpr v n]
                deriving (Generic)

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
  UnaryApp UnaryOp (Expr v n) |
  MulExp (Expr v n) (Expr v n) |
  SinExp (Expr v n)
  deriving Generic

-- | An angular function of the form @c + n*sin(theta + alpha)@
-- where @theta@, and @n@ are linear terms, @alpha@ and @c@ are constants.
type LinearMap v n = M.HashMap v (LinExpr v n)
type TrigEq v n = (Period v n, Amplitude v n, Phase n, n)
type TrigEq2 v n = M.HashMap (Period v n)
                   (M.HashMap v (Expr v n))

pattern LinearE l = Expr l [] []
pattern ConstE c = Expr (LinExpr c []) [] []
pattern LConst c = LinExpr c []

instance (Hashable v, Hashable n) => Hashable (LinExpr v n)
instance (Hashable v, Hashable n) => Hashable (NonLinExpr v n)
instance Hashable UnaryOp
instance (Hashable v, Hashable n) => Hashable (Expr v n)
instance Hashable SimpleVar

-- | A simple String wrapper, which will print formulas more cleanly.
instance Show SimpleVar where
  show (SimpleVar s) = s

-- | This hidden datatype represents a system of equations.  It
-- contains linear dependencies on variables as well as nonlinear
-- equations. The following terminology is used from /metafont/:
-- 
--   * /known variable/: A variable who's dependency is just a number.
--   
--   * /dependend variable/: A variable which depends linearly on other variables.
--
--   * /independend variable/: any other variable.
--
-- A /dependend/ variable can only depend on other /independend/
-- variables.  Nonlinear equations will be simplified by substituting
-- and evaluating known variables, or by reducing some trigonometric
-- equations to linear equations.
data Dependencies v n = Dependencies
                        (M.HashMap v (H.HashSet v))
                        (LinearMap v n)
                        [TrigEq v n]
                        (TrigEq2 v n)
                        [Expr v n]
                        
-- | An error type for '===', '=&=' and 'addEquation':
data DepError v n =
  -- | The variable is not defined.
  UndefinedVar v |
  -- | The variable is defined but dependend an other variables.
  UnknownVar v n |
  -- | The equation was reduced to the
  -- impossible equation `a == 0` for nonzero a, which means the
  -- equation is inconsistent with previous equations.
  InconsistentEq n |
  -- | The equation was reduced to the redundant equation `0 == 0`,
  -- which means it doesn't add any information.
  RedundantEq
  deriving Typeable

instance (Show v, Show n, Typeable v, Typeable n) => Exception (DepError v n)

instance (Ord n, Num n, Eq n, Show v, Show n) => Show (Expr v n) where
  show e = show (toSimple e)

-- | A monad transformer for solving equations.  Basicly just a state and exception monad transformer over `Dependencies` and `DepError`.
newtype MFSolverT v n m a = MFSolverT (StateT (Dependencies v n) (ExceptT (DepError v n) m) a)
                            deriving (Functor, Applicative, Monad, MonadIO, MonadState (Dependencies v n),
                                      MonadError (DepError v n), MonadReader s, MonadWriter s,
                                      MonadCont)

instance MonadTrans (MFSolverT v n) where
  lift = MFSolverT . lift. lift

runSolverT :: MFSolverT v n m a -> Dependencies v n -> m (Either (DepError v n) (a, Dependencies v n))
runSolverT (MFSolverT s) = runExceptT . runStateT s 

-- | A monad for solving equations.  Basicly just a state and exception monad over `Dependencies` and `DepError`.
type MFSolver v n a = MFSolverT v n Identity a

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
  negate = mulExpr (ConstE (-1))
  abs = unExpr Abs
  signum = unExpr Signum
  fromInteger = ConstE . fromInteger

instance (Floating n, Ord n, Ord v) => Fractional (Expr v n) where
  recip = unExpr Recip
  fromRational = ConstE . fromRational

instance (Floating n, Ord n, Ord v) => Floating (Expr v n) where
  pi = ConstE pi
  exp = unExpr Exp
  log = unExpr Log
  sin = sinExpr
  cos a = sinExpr (a + ConstE (pi/2))
  cosh = unExpr Cosh
  atanh = unExpr Atanh
  tan = unExpr Tan
  sinh = unExpr Sinh
  asin = unExpr Asin
  acos = unExpr Acos
  asinh = unExpr Asinh
  acosh = unExpr Acosh
  atan = unExpr Atan

instance (Show n, Floating n, Ord n, Ord v, Show v) =>Show (Dependencies v n) where
  show dep@(Dependencies _ lin _ _ _) = 
    unlines (map showLin (M.toList lin) ++
             map showNl (nonlinearEqs dep))
    where showLin (v, e) = show v ++ " = " ++ show (LinearE e)
          showNl e = show e ++ " = 0"

instance (Show n, Show v) => Show (DepError v n) where
  show (InconsistentEq a) =
    "Inconsistent equations, off by " ++ show a
  show RedundantEq =
    "Redundant Equation."
  show (UndefinedVar v) =
    error ("Variable is undefined: " ++ show v)
  show (UnknownVar v n) =
    error ("Value of variable not known: " ++ show v ++ " = " ++ show n)

addSimple :: (Num t1, Eq t1) => SimpleExpr t t1 -> SimpleExpr t t1 -> SimpleExpr t t1
addSimple (Const 0) e = e
addSimple e (Const 0) = e
addSimple e1 e2 = SEBin Add e1 e2

seHasVar :: Eq v => v -> SimpleExpr v t -> Bool
seHasVar v1 (Var v2) = v1 == v2
seHasVar _ (Const _) = False
seHasVar v (SEBin _ e1 e2) =
  seHasVar v e1 ||
  seHasVar v e2
seHasVar v (SEUn _ e) = seHasVar v e

-- | The expression contains the given variable.
hasVar :: (Num t, Eq v, Eq t) => v -> Expr v t -> Bool
hasVar v = seHasVar v . toSimple

linToSimple :: (Num n, Eq n) => LinExpr v n -> SimpleExpr v n
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
        angle = linToSimple (LinExpr alpha theta)

nonlinToSimple :: (Num n, Eq n) => NonLinExpr v n -> SimpleExpr v n
nonlinToSimple (UnaryApp o e) =
  SEUn o (toSimple e)
nonlinToSimple (MulExp e1 e2) =
  SEBin Mul (toSimple e1) (toSimple e2)
nonlinToSimple (SinExp e) =
  SEUn Sin (toSimple e)

-- | Convert an `Expr` to a `SimpleExpr`.
toSimple :: (Num n, Eq n) => Expr v n -> SimpleExpr v n
toSimple (Expr lin trig nonlin) =
  linToSimple lin `addSimple`
  foldr (addSimple.trigToSimple)
  (Const 0) trig `addSimple`
  foldr (addSimple.nonlinToSimple)
  (Const 0) nonlin

evalBin :: (Floating n) => BinaryOp -> n -> n -> n
evalBin Add = (+)
evalBin Mul = (*)

evalUn :: (Floating n) => UnaryOp -> n -> n
evalUn Sin = sin
evalUn Abs = abs
evalUn Recip = recip
evalUn Signum = signum
evalUn Exp = exp
evalUn Log = log
evalUn Cos = cos
evalUn Cosh = cosh
evalUn Atanh = atanh
evalUn Tan = tan
evalUn Sinh = sinh
evalUn Asin = asin
evalUn Acos = acos
evalUn Asinh = asinh
evalUn Acosh = acosh
evalUn Atan = atan

-- | evaluate a simple expression using the given substitution.
evalSimple :: Floating m => (n -> m) -> (v -> m) -> SimpleExpr v n -> m
evalSimple _ s (Var v) = s v
evalSimple g _ (Const c) = g c
evalSimple g s (SEBin f e1 e2) =
  evalBin f (evalSimple g s e1) (evalSimple g s e2)
evalSimple g s (SEUn f e) =
  evalUn f (evalSimple g s e)

-- | Make a expression from a simple expression.
fromSimple :: (Floating n, Ord n, Ord v) => SimpleExpr v n -> Expr v n
fromSimple = evalSimple makeConstant makeVariable

-- | Evaluate the expression given a variable substitution.
evalExpr :: (Floating n) => (v -> n) -> SimpleExpr v n -> n
evalExpr = evalSimple id

zeroTerm :: (Num n) => LinExpr v n
zeroTerm = LConst 0

-- | Create an expression from a constant
makeConstant :: n -> Expr v n
makeConstant = ConstE

-- | Create an expression from a variable
makeVariable :: Num n => v -> Expr v n
makeVariable v = LinearE $ LinExpr 0 [(v, 1)]

trigExpr :: (Num n) => [TrigTerm v n] -> Expr v n
trigExpr t = Expr zeroTerm t []

nonlinExpr :: Num n => [NonLinExpr v n] -> Expr v n
nonlinExpr = Expr zeroTerm []

isConst :: LinExpr v n -> Bool
isConst (LConst _) = True
isConst _ = False

linVars :: LinExpr v n -> [v]
linVars (LinExpr _ v) = map fst v

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
       Just (_, LConst 0) -> rest
       Just (gamma, o) ->
         mergeTerms (gamma, o) rest
       Nothing ->
         (beta, m) : mergeTerms (alpha, n) rest
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
mulExpr (ConstE c) (Expr lt2 trig []) =
  Expr (mulLinExpr c lt2)
  (map (mulConstTrig c) trig) []

mulExpr (Expr lt2 trig []) (ConstE c) =
  Expr (mulLinExpr c lt2)
  (map (mulConstTrig c) trig) []

-- linear * (constant + trig)
mulExpr (LinearE lt) (Expr (LConst c) trig []) =
  LinearE (mulLinExpr c lt) +
  foldr ((+).mulLinTrig lt) 0 trig

mulExpr (Expr (LConst c) trig []) (LinearE lt) =
  LinearE (mulLinExpr c lt) +
  foldr ((+).mulLinTrig lt) 0 trig

-- anything else
mulExpr e1 e2 = nonlinExpr [MulExp e1 e2]
      
sinExpr :: Floating n => Expr v n -> Expr v n
sinExpr (Expr (LinExpr c t) [] [])
  | null t = ConstE (sin c)
  | otherwise = trigExpr [(t, [(c, LinExpr 1 [])])]
sinExpr e = nonlinExpr [SinExp e]

unExpr :: Floating n => UnaryOp -> Expr v n -> Expr v n
unExpr f (ConstE c) = ConstE (evalUn f c)
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
  let period2 = LinearE $ substVarLin s (LinExpr 0 period)
      terms2 = map (fmap $ LinearE . substVarLin s) terms
  in foldr (\(p,a) -> (+ (a * sin (ConstE p + period2))))
     0 terms2

subst :: (Ord n, Ord v, Floating n) => (v -> Maybe (LinExpr v n)) -> Expr v n -> Expr v n
subst s (Expr lt trig nl) =
  LinearE (substVarLin s lt) +
  foldr ((+).substVarTrig s) 0 trig +
  foldr ((+).substVarNonLin s) 0 nl

-- | An empty system of equations.
noDeps :: Dependencies v n
noDeps = Dependencies M.empty M.empty [] M.empty []

simpleSubst :: Eq a => a -> b -> a -> Maybe b
simpleSubst x y z
  | x == z = Just y
  | otherwise = Nothing

trigToExpr :: (Ord n, Ord v, Floating n) => TrigEq v n -> Expr v n
trigToExpr (p, a, ph, c) =
  LinearE a * sin(LinearE $ LinExpr ph p) +
  ConstE c

trig2ToExpr :: (Ord v, Floating n, Ord n) => M.HashMap v (Expr v n) -> [Expr v n]
trig2ToExpr =
  map (\(v,e)-> makeVariable v-e)
  . M.toList

addEqs :: (Hashable v, Hashable n, RealFrac (Phase n), Ord v, Floating n) => Dependencies v n -> [Expr v n] -> Either (DepError v n) (Dependencies v n)
addEqs = foldM addEquation

-- | @addEquation d e@: Add the equation @e = 0@ to the system d.
addEquation :: (Hashable n, Hashable v, RealFrac (Phase n), Ord v,
          Floating n) =>
         Dependencies v n
         -> Expr v n -> Either (DepError v n) (Dependencies v n)
addEquation deps@(Dependencies _ lin _ _ _) expr =
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

-- substitute v for lt in all linear equations
-- if insertp is true, then add v = tl to equations
substDep :: (Hashable v, Ord v, Num n, Eq n) =>
             M.HashMap v (H.HashSet v) -> M.HashMap v (LinExpr v n)
             -> v -> LinExpr v n -> Bool 
             -> (M.HashMap v (H.HashSet v), LinearMap v n)
substDep vdep lin v lt insertp =
       -- variables that depend on v
  let depVars = fromMaybe H.empty (M.lookup v vdep)
      -- substitute v in all dependend variables and (optionally) add
      -- v as dependend variable
      lin' = (if insertp then M.insert v lt
              else id) $
             H.foldl' (flip $ M.adjust $
                       substVarLin $
                       simpleSubst v lt)
             lin depVars
      -- add dependency link from independend variables to the
      -- substituted equations and (optionally) v, and remove v (since
      -- it has become dependend, so no variable can depend on it).
      depVars2 | insertp = H.insert v depVars
               | otherwise = depVars
      -- exclude dependend variable v if k has been canceled
      tryUnion k m1 m2 =
        let xs = H.intersection m1 m2
            hasvar v2 = case M.lookup v2 lin' of
              Nothing -> False
              Just (LinExpr _ vs) ->
                any ((==k).fst) vs
        in H.filter hasvar xs
           `H.union` H.difference m1 xs
           `H.union` H.difference m2 xs
      vdep' = H.foldl'
              (\mp k -> M.insertWith (tryUnion k) k depVars2 mp)
              (M.delete v vdep)
              (H.fromList $ linVars lt)
  in (vdep', lin')

addEq0 :: (Hashable v, Hashable n, RealFrac (Phase n), Ord v, Floating n) => Dependencies v n -> Expr v n -> Either (DepError v n) (Dependencies v n)
-- adding a constant equation
addEq0 _  (ConstE c) =
  Left $ if c == 0 then RedundantEq
         else InconsistentEq c

-- adding a linear equation
addEq0 (Dependencies vdep lin trig trig2 nonlin) (Expr lt [] []) =
  let (v, _, lt2) = splitMax lt
      (vdep', lin') = substDep vdep lin v lt2 True
      
      -- Add nonlinear equations again to the system.
      trig' = map trigToExpr trig
      trig2' = concatMap trig2ToExpr $ M.elems trig2
  in addEqs (Dependencies vdep' lin' [] M.empty []) (trig'++trig2'++nonlin)

-- adding a sine equation
addEq0 deps@(Dependencies vdep lin trig trig2 nl)
  (Expr (LinExpr c lt) [(theta, [(alpha, LConst n)])] []) =
  if null lt then
    -- reduce a sine to linear equation
    addEq0 deps (LinearE $ LinExpr (alpha - asin (-c/n)) theta)
  else
    -- add a variable dependency on the sine equation
    case M.lookup theta trig2 of
     -- no sine with same period
     Nothing -> addSin (LinExpr c lt) alpha n
     Just map2 ->
       case foldr ((+).doSubst)
            (ConstE c +
             ConstE n *
             sin (LinearE $ LinExpr alpha theta))
            lt of
        Expr lt2 [(_, [(alpha2, LConst n2)])] []
          | not $ isConst lt2
          -> addSin lt2 alpha2 n2
        e2 -> addEq0 deps e2
       where
         doSubst (v,c2) = case M.lookup v map2 of
           Nothing -> makeVariable v * ConstE c2
           Just e2 -> e2 * ConstE c2
  where
    addSin l' a' n' =
      let (v, c', r) = splitMax l'
          trig2' = M.insertWith M.union theta
                   (M.singleton v $
                    Expr r [(theta, [(a', LinExpr (n'/negate c') [])])] [])
                   trig2
      in Right $ Dependencies  vdep lin trig trig2' nl

--  adding the first sine equation
addEq0 (Dependencies d lin [] trig2 nl)
  (Expr (LConst c) [(theta, [(alpha, n)])] []) =
  Right $ Dependencies d lin [(theta, n, alpha, c)] trig2 nl

-- try reducing this equation with another sine equation
addEq0 (Dependencies deps lin trig trig2 nl)
  (Expr (LConst x) [(theta, [(a, n)])] []) =
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
       lin1   = LinearE $ LinExpr (-theta2) theta
       lin2   = LinearE n - ConstE n2
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

deleteDep :: (Hashable k, Hashable b, Eq k, Eq b) =>
             M.HashMap b (H.HashSet k)
          -> M.HashMap k (LinExpr b n) -> k
          -> Maybe (M.HashMap b (H.HashSet k), M.HashMap k (LinExpr b n), LinExpr b n)
deleteDep vdep lin v =
  case M.lookup v lin of
   Nothing -> Nothing
   Just lt -> Just (vdep', lin', lt)
     where
       -- delete equation of v
       lin' = M.delete v lin
       -- delete v from dependencies
       vdep' = H.foldl'
               (flip $ M.adjust $ H.delete v)
               vdep (H.fromList $ linVars lt)

-- | Eliminate an variable from the equations.  Returns the eliminated
-- equations.  Before elimination it performs substitution to minimize
-- the number of eliminated equations.
-- 
--__Important__: this function is
-- still experimental and mostly untested.
eliminate :: (Hashable n, Show n, Hashable v, RealFrac (Phase n), Ord v, Show v,
              Floating n) => Dependencies v n -> v -> (Dependencies v n, [Expr v n])
eliminate (Dependencies vdep lin trig trig2 nonlin) v
  | Just (vdep', lin', lt) <- deleteDep vdep lin v =
    -- v is dependend, so doesn't appear in other equations
    (Dependencies vdep' lin' trig trig2 nonlin,
     [LinearE lt - makeVariable v])
  | Just vars <- M.lookup v vdep,
    (v2:_) <- H.toList vars =
      -- v is independend, and appears in a linear equation
      case deleteDep vdep lin v2 of
       Nothing ->
         error $ "Internal error: found empty dependency on " ++ show v2
       Just (vdep', lin', lt) ->
         -- rearrange the deleted equation in terms of v
         let lt2 = snd $ reArrange v2 lt v
             -- substitute v in all equations
             (vdep'', lin'') = substDep vdep' lin' v lt2 False
             trig' = map trigToExpr trig
             trig2' = concatMap trig2ToExpr $ M.elems trig2
             deps = Dependencies vdep'' lin'' [] M.empty []
             e = [LinearE lt2 - makeVariable v]
          -- use addEq0 since substitution is unnecessary
         in case foldM addEq0
                 deps $
                 map (subst $ simpleSubst v lt2)
                 (trig'++trig2'++nonlin) of
             Left _ -> (deps, e) --shouldn't happen
             Right d -> (d, e)
  | otherwise =
      let (l, trig2') =
            M.foldrWithKey trigFold
            ([], M.empty) trig2
          trigFold p t (l2, m2) =
            let (l3, m1) = elimTrig p t v
                mp | M.null m1 = m2
                   | otherwise = M.insert p m1 m2
            in (l3++l2, mp)
            
          (nlWith, nlWithout) =
            partition (hasVar v) $
            map trigToExpr trig ++ nonlin
          deps = Dependencies vdep lin [] trig2' []
      in case foldM addEq0 deps
              nlWithout of
             Left _ -> (deps, nlWith++l) --shouldn't happen
             Right d -> (d, nlWith++l)

-- v2 = c2*v + b + c
reArrange :: (Show v, Ord v, Fractional n, Eq n) =>
             v -> LinExpr v n -> v -> (n, LinExpr v n)
reArrange v2 (LinExpr c vars) v =
  case find ((==v).fst.fst) $ select vars of
   Nothing ->
     error $ "Internal error: variable " ++ show v ++
     " not in linear expression "
   Just ((_,c2), r) ->
     (c2,
      LinExpr (c/negate c2) r
      `addLin` LinExpr 0 [(v2, 1/c2)])

reArrangeTrig :: (Show v, Ord t1, Ord v, Floating t1) => v -> Expr v t1 -> v -> Expr v t1
reArrangeTrig v2 (Expr lt trig _) v =
  let (c2, lt2) = reArrange v2 lt v
  in LinearE lt2 - trigExpr trig / ConstE c2
  
elimTrig :: (Show v, Ord v, Hashable v, Floating n, Ord n) =>
            Period v n -> M.HashMap v (Expr v n) -> v
         -> ([Expr v n], M.HashMap v (Expr v n))
elimTrig p m v
  -- period contains the variable, remove all eqs
  | any ((==v).fst) p =
      (trig2ToExpr m, M.empty)
  -- the variable is dependend in:
  -- v = e (== sin(p+const) + linear)
  -- remove the eq
  | Just e <- M.lookup v m =
      ([makeVariable v - e],
       M.delete v m)
  -- the variable is independent in:
  -- v2 = e (== sin(p+const) + const*v + linear)
  -- rearrange, and substitute
  | Just (v2, e) <-
    find (hasVar v.snd) $ M.toList m =
      let e2 = reArrangeTrig v2 e v
          substOne (v3, c)
            | v == v3 = e2 * ConstE c
            | otherwise = makeVariable v3 * ConstE c
          doSubst (Expr (LinExpr c lt) trig _) =
            foldr ((+).substOne) 
            (ConstE c + trigExpr trig) lt
      in ([makeVariable v - e],
          M.map doSubst $ M.delete v2 m)
  -- variable not found
  | otherwise =
    ([], m)

dmod :: RealFrac a => a -> a -> a
dmod a b = abs((a/b) - fromInteger (round (a/b)) * b)

-- put the variable with the maximum coefficient on the lhs of the
-- equation
splitMax :: (Ord b, Fractional b, Eq v) => LinExpr v b -> (v, b, LinExpr v b)
splitMax (LinExpr c t) =
  let ((v,c2),r) = maximumBy (compare `on` (abs.snd.fst)) $
                   select t
  in (v, c2,
      LinExpr (-c/c2) $
      map (fmap (negate.(/c2))) r)
      
-- | Return True if the variable is known or dependend.
varDefined :: (Eq v, Hashable v) => v -> Dependencies v n -> Bool
varDefined v (Dependencies _ dep _ _ _) =
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
getKnown :: (Eq v, Hashable v) => v -> Dependencies v n -> Either [v] n
getKnown var (Dependencies _ lin _ _ _) =
  case M.lookup var lin of
    Nothing -> Left  []
    Just (LinExpr a []) ->
      Right a
    Just (LinExpr _ v) ->
      Left $ map fst v

-- | Return all nonlinear equations @e_i@, where @e_i = 0@.
nonlinearEqs :: (Ord n, Ord v, Floating n) => Dependencies v n -> [Expr v n]
nonlinearEqs  (Dependencies _ _ trig trig2 nl) =
  map trigToExpr trig ++
  map (\(v, e) -> makeVariable v - e) 
  (concatMap M.toList (M.elems trig2)) ++
  nl
  
-- | Show all variables and equations.  Useful in combination with `execSolver`.
showVars :: (Show n, Show v, Ord n, Ord v, Floating n) => Either (DepError v n) (Dependencies v n) -> IO ()
showVars (Left e) = print e
showVars (Right dep) = print dep

-- | Get the dependencies from a state monad.  Specialized version of `get`.
dependencies :: (MonadState (Dependencies v n) m) => m (Dependencies v n)
dependencies = get

-- | Return the value of the variable or throw an error.
getValue :: (MonadState (Dependencies v n) m,
             MonadError (DepError v n) m,
             Eq v, Hashable v) =>
            v -> m n
getValue v = do
  v2 <- getKnownM v
  case v2 of
   Right e -> return e
   Left _ -> throwError $ UndefinedVar v

-- | Monadic version of `varDefined`.
varDefinedM :: (MonadState (Dependencies v n) m, Hashable v, Eq v) =>
               v -> m Bool
varDefinedM v = varDefined v `liftM` dependencies

-- | Monadic version of `getKnown`.
getKnownM :: (MonadState (Dependencies v n) m, Hashable v, Eq v) =>
             v -> m (Either [v] n)
getKnownM v = getKnown v `liftM` dependencies

-- | Monadic version of `eliminate`.
eliminateM :: (MonadState (Dependencies v n) m, Hashable n, Hashable v,
               Show n, Show v, RealFrac n, Ord v, Floating n) =>
              v -> m [Expr v n]
eliminateM v = do
  dep <- dependencies
  let (dep2, e) = eliminate dep v
  put dep2
  return e

infixr 1 === , =&=

-- | Make the expressions on both sides equal
(===) :: (MonadState (Dependencies v n) m,
          MonadError (DepError v n) m,
          Eq v, Hashable v, Hashable n,
          RealFrac n, Floating n, Ord v) =>
         Expr v n -> Expr v n -> m ()
(===) lhs rhs = do
  deps <- dependencies
  case addEquation deps (lhs - rhs) of
   Left e -> throwError e
   Right dep -> put dep

-- | Make the pairs of expressions on both sides equal. No error is
-- signaled if the equation for one of the sides is `Redundant` for
-- example in (x, 0) == (y, 0).
(=&=) :: (MonadState (Dependencies v n) m,
          MonadError (DepError v n) m,
          Eq v, Hashable v, Hashable n,
          RealFrac n, Floating n, Ord v) =>
         (Expr v n, Expr v n) -> (Expr v n, Expr v n) -> m ()
(=&=) (a, b) (c, d) =
  do ignore $ a === c
     b === d

-- | Succeed even when trowing a `RedundantEq` error.
ignore :: MonadError (DepError v n) m => m () -> m ()
ignore m = m `catchError` (
  \e -> case e of
         RedundantEq -> return ()
         _ -> throwError e)

-- | run the solver.
runSolver :: MFSolver v n a -> Dependencies v n -> Either (DepError v n) (a, Dependencies v n)
runSolver s = runIdentity . runSolverT s
           
-- | Return the result of solving the equations, or throw the error as an exception.  Monadic version.
unsafeSolveT :: (Show n, Show v, Typeable n, Typeable v, Monad m) =>
                Dependencies v n -> MFSolverT v n m a -> m a
unsafeSolveT dep s = do
  res <- runSolverT s dep
  case res of
   Right (v, _) -> return v
   Left e -> throw e

-- | Return the result of solving the equations or an error.  Monadic version.
evalSolverT :: Functor f =>
               MFSolverT v n f b
            -> Dependencies v n -> f (Either (DepError v n) b)
evalSolverT s dep =
  fmap fst <$> runSolverT s dep 

-- | Run the solver and return the dependencies or an error.  Monadic version.
execSolverT :: Functor m =>
               MFSolverT v n m a
            -> Dependencies v n -> m (Either (DepError v n) (Dependencies v n))
execSolverT s dep =
  fmap snd <$> runSolverT s dep

-- | Return the result of solving the equations, or throw the error as an exception.
unsafeSolve :: (Typeable n, Typeable v, Show n, Show v) =>
               Dependencies v n -> MFSolver v n a -> a
unsafeSolve dep = runIdentity . unsafeSolveT dep

-- | Return the result of solving the equations or an error.
evalSolver :: MFSolver v n a
           -> Dependencies v n -> Either (DepError v n) a
evalSolver s = runIdentity . evalSolverT s

-- | Run the solver and return the dependencies or an error.
execSolver :: MFSolver v n a
           -> Dependencies v n -> Either (DepError v n) (Dependencies v n)
execSolver s = runIdentity . execSolverT s

