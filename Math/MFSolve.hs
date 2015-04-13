{-# LANGUAGE DeriveGeneric, PatternGuards #-}

{-|
Module      : Math.MFSolve
Description : solving linear equations in an iterative way, à la metafont.
Copyright   : (c) Kristof Bastiaensen, 2014
License     : BSD-3
Maintainer  : kristof@resonata.be
Stability   : unstable
Portability : portable

This module implements an equation solver and calculator not unlike that used in D.E.Knuth's metafont. Like metafont, it can solve linear equations, and evaluate nonlinear expressions.  In addition to metafont, it also solves for angles, and makes the solution independend of the order of the equations.
-}

module Math.MFSolve
       (SimpleExpr(..), Expr, UnaryOp(..), BinaryOp(..),
        Dependencies, DepError(..), SimpleVar(..),
        getKnown, knownVars, varDefined, nonlinearEqs,
        simpleExpr, emptyDeps, makeVariable, makeConstant,
        (===), (=&=), solveEq, showVars)
where
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as H
import GHC.Generics
import Data.Hashable
import Data.Maybe
import Data.List
import Data.Function(on)
import Control.Monad
import Debug.Trace

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
data Expr v n = Expr (LinTerm v n) [TrigTerm v n] [NonLinTerm v n]
                deriving Generic

-- A linear term of several variables.
-- For example: @2*a + 3*b + 2@ would be represented as
-- @DependencyList 2 [(a, 2), (b, 3)]@.
data LinTerm v n = LinTerm n [(v, n)]
                 deriving (Generic, Eq, Show)
type Period v n = [(v, n)]
type Phase n = n
type Amplitude v n = LinTerm v n

-- A sum of sinewaves with the same period (a linear sum of several
-- variables), but possibly different (constant) phase.  For example
-- @(2*a+b) sin (x+y) + 2*b*sin(x+y+pi)@ would be represented by:
-- @TrigTerm [(x,1),(y,1)] [(0, LinTerm 0 [(a, 2), (b, 1)]),
-- (pi, LinTerm 0 [(b, 2)])@
type TrigTerm v n = (Period v n, [(Phase n, Amplitude v n)])

-- Any other term
data NonLinTerm v n = 
  UnaryApp (UnaryFun n) (Expr v n) |
  MulExp (Expr v n) (Expr v n) |
  SinExp (Expr v n)
  deriving Generic

-- | An angular function of the form @c + n*sin(theta + alpha)@
-- where @theta@, and @n@ are linear terms, @alpha@ and @c@ are constants.
type LinearMap v n = M.HashMap v (LinTerm v n)
type TrigEq v n = (Period v n, Amplitude v n, Phase n, n)


instance (Hashable v, Hashable n) => Hashable (LinTerm v n)
instance (Hashable v, Hashable n) => Hashable (NonLinTerm v n)
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
  | elem op ops = "(" ++ show e ++ ")"
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
    where space = case e1 of
                   Const _ -> ""
                   _ -> " "
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
  show dep@(Dependencies _ lin _ _) = 
    unlines (map showLin (M.toList lin) ++
             map showNl (nonlinearEqs dep))
    where showLin (v, e) = show v ++ " = " ++ (show $ linExpr e)
          showNl e = show e ++ " = 0"

addSimple :: (Num t1, Eq t1) => SimpleExpr t t1 -> SimpleExpr t t1 -> SimpleExpr t t1
addSimple (Const 0) e = e
addSimple e (Const 0) = e
addSimple e1 e2 = SEBin Add e1 e2

linToSimple :: (Num t1, Eq t1) => LinTerm t t1 -> SimpleExpr t t1
linToSimple (LinTerm v t) =
  (Const v) `addSimple`
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
                linToSimple (LinTerm 0 theta)
              | otherwise =
                SEBin Add (linToSimple (LinTerm 0 theta))
                (Const alpha)

nonlinToSimple :: (Num n, Eq n) => NonLinTerm v n -> SimpleExpr v n
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

zeroTerm :: (Num n) => LinTerm v n
zeroTerm = LinTerm 0 []

linExpr :: LinTerm v n -> Expr v n
linExpr lt = Expr lt [] []

-- | Create an expression from a constant
makeConstant :: n -> Expr v n
makeConstant c = linExpr (LinTerm c [])

-- | Create an expression from a variable
makeVariable :: Num n => v -> Expr v n
makeVariable v = linExpr (LinTerm 0 [(v, 1)])

trigExpr :: (Num n) => [TrigTerm v n] -> Expr v n
trigExpr t = Expr zeroTerm t []

nonlinExpr :: Num n => [NonLinTerm v n] -> Expr v n
nonlinExpr n = Expr zeroTerm [] n

getConst :: LinTerm t a -> Maybe a
getConst (LinTerm a []) = Just a
getConst _ = Nothing

getLin :: Expr t n -> Maybe (LinTerm t n)
getLin (Expr lt [] []) = Just lt
getLin _ = Nothing

getConstExpr :: Expr t b -> Maybe b
getConstExpr e = getLin e >>= getConst

addLin :: (Ord v, Num n, Eq n) => LinTerm v n -> LinTerm v n -> LinTerm v n
addLin (LinTerm c1 terms1) (LinTerm c2 terms2) =
  LinTerm (c1+c2) terms3 where
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
addTrigTerms :: (Ord a, Ord t, Floating a) => [(a, LinTerm t a)] -> [(a, LinTerm t a)] -> [(a, LinTerm t a)]
addTrigTerms [] p = p
addTrigTerms terms terms2 =
  foldr mergeTerms terms terms2
  where
    mergeTerms (alpha, n) ((beta, m):rest) =
      case addTrigTerm alpha n beta m of
       Just (_, LinTerm 0 []) -> rest
       Just (gamma, o) ->
         mergeTerms (gamma, o) rest
       Nothing -> (beta, m) : mergeTerms (alpha, n) rest
    mergeTerms a [] = [a]

addTrigTerm :: (Ord a, Ord t, Floating a) => a -> LinTerm t a -> a -> LinTerm t a -> Maybe (a, LinTerm t a)
addTrigTerm alpha n beta m
  | alpha == beta =
    Just (alpha, addLin n m)
  | Just r <- termIsMultiple n m =
      let gamma = atan (divident/divisor) +
                  (if divisor < 0 then pi else 0)
          divident = r*sin alpha + sin beta
          divisor = r*cos alpha + cos beta
          o = sqrt(divident*divident + divisor*divisor)
      in Just (gamma, mulLinTerm o m)
  | otherwise = Nothing

-- compare if the linear term is a multiple of the other, within roundoff                
termIsMultiple :: (Ord a, Fractional a, Eq t) => LinTerm t a -> LinTerm t a -> Maybe a
termIsMultiple (LinTerm _ _) (LinTerm 0 []) = Nothing
termIsMultiple (LinTerm 0 []) (LinTerm _ _) = Nothing
termIsMultiple (LinTerm 0 r1@((_, d1):_)) (LinTerm 0 r2@((_, d2):_))
  | compareBy r1 r2 (compareTerm (d1/d2)) =
      Just (d1/d2)
termIsMultiple (LinTerm c1 r1) (LinTerm c2 r2)
  | compareBy r1 r2 (compareTerm (c1/c2)) =
      Just (c1/c2)
  | otherwise = Nothing

compareTerm :: (Ord a1, Fractional a1, Eq a) => a1 -> (a, a1) -> (a, a1) -> Bool
compareTerm ratio (v3,c3) (v4, c4) = 
  v3 == v4 && (abs(c3 - (c4 * ratio)) < abs c3*(2e-50))

compareBy :: [a] -> [b] -> (a -> b -> Bool) -> Bool
compareBy [] [] _ = True
compareBy (e:l) (e2:l2) f =
  f e e2 && compareBy l l2 f
compareBy _ _ _ = False
        
-- multiply a linear term by a constant.
mulLinTerm :: Num n => n -> LinTerm v n -> LinTerm v n
mulLinTerm x (LinTerm e terms) =
  LinTerm (e*x) $ map (fmap (*x)) terms

-- multiply all sines with the constant
-- constant multiplier
mulConstTrig :: (Ord n, Num n) => n -> TrigTerm v n -> TrigTerm v n
mulConstTrig c (theta, terms) =  (theta, tt) where
  tt = map (fmap (mulLinTerm c)) terms

mulLinTrig :: (Ord n, Ord v, Floating n) => LinTerm v n -> TrigTerm v n -> Expr v n
mulLinTrig lt (theta, terms) =
  -- linear multiplier
  foldr (+) 0 (map mul1 terms)
  where
    -- constant amplitude
    mul1 (alpha, LinTerm c []) =
      trigExpr [(theta, [(alpha, mulLinTerm c lt)])]
    -- linear amplitude
    mul1 t =
      nonlinExpr [MulExp (trigExpr [(theta, [t])])
                      (Expr lt [] [])]

-- constant * (linear + trig)
mulExpr :: (Ord a, Ord t, Floating a) => Expr t a -> Expr t a -> Expr t a
mulExpr (Expr lt [] []) (Expr lt2 trig []) 
  | Just c <- getConst lt =
      Expr (mulLinTerm c lt2)
      (map (mulConstTrig c) trig) []

mulExpr (Expr lt2 trig []) (Expr lt [] []) 
  | Just c <- getConst lt =
      Expr (mulLinTerm c lt2)
      (map (mulConstTrig c) trig) []

-- linear * (constant + trig)
mulExpr (Expr lt [] []) (Expr lt2 trig []) 
  | Just c <- getConst lt2 =
      linExpr (mulLinTerm c lt) +
      foldr ((+).mulLinTrig lt) 0 trig

mulExpr (Expr lt2 trig []) (Expr lt [] []) 
  | Just c <- getConst lt2 =
      linExpr (mulLinTerm c lt) +
      foldr ((+).mulLinTrig lt) 0 trig

-- anything else
mulExpr e1 e2 = nonlinExpr [MulExp e1 e2]
      
sinExpr :: Floating n => Expr v n -> Expr v n
sinExpr (Expr (LinTerm c t) [] [])
  | null t = makeConstant (sin c)
  | otherwise = trigExpr [(t, [(c, LinTerm 1 [])])]
sinExpr e = nonlinExpr [SinExp e]

unExpr :: Num n => UnaryFun n -> Expr v n -> Expr v n
unExpr (UnaryFun _ f) e
  | Just c <- getConstExpr e = makeConstant (f c)
unExpr f e = nonlinExpr [UnaryApp f e]

substVarLin :: (Ord v, Num n, Eq n) => (v -> Maybe (LinTerm v n)) -> LinTerm v n -> LinTerm v n
substVarLin s (LinTerm a terms) =
  let substOne (v, c) =
        maybe (LinTerm 0 [(v, c)]) (mulLinTerm c) (s v)
  in foldr (addLin.substOne) (LinTerm a []) terms

substVarNonLin :: (Ord n, Ord v, Floating n) => (v -> Maybe (LinTerm v n)) -> NonLinTerm v n -> Expr v n
substVarNonLin s (UnaryApp f e1) =
  unExpr f (subst s e1)
substVarNonLin s (MulExp e1 e2) =
  mulExpr (subst s e1) (subst s e2)
substVarNonLin s (SinExp e1) =
  sinExpr (subst s e1)

substVarTrig :: (Ord v, Ord n, Floating n) => (v -> Maybe (LinTerm v n)) -> ([(v, n)], [(n, LinTerm v n)]) -> Expr v n
substVarTrig s (period, terms) =
  let period2 = linExpr $ substVarLin s (LinTerm 0 period)
      terms2 = map (fmap $ linExpr.substVarLin s) terms
  in foldr (\(p,a) -> (+ (a * sin (makeConstant p + period2))))
     0 terms2

subst :: (Ord n, Ord v, Floating n) => (v -> Maybe (LinTerm v n)) -> Expr v n -> Expr v n
subst s (Expr lt trig nl) =
  (linExpr $ substVarLin s lt) +
  foldr ((+).substVarTrig s) 0 trig +
  foldr ((+).substVarNonLin s) 0 nl

-- | An empty set of dependencies.
emptyDeps :: Dependencies v n
emptyDeps = Dependencies M.empty M.empty [] []

simpleSubst :: Eq a => a -> b -> a -> Maybe b
simpleSubst x y z
  | x == z = Just y
  | otherwise = Nothing

-- | Make the expressions on both sides equal, and add the result to the Set of
-- dependencies.
(===) :: (Hashable v, RealFrac (Phase n), Ord v, Floating n) => Expr v n -> Expr v n -> Dependencies v n -> Either (DepError n) (Dependencies v n)
(===) lhs rhs deps@(Dependencies _ lin _ _) =
      -- substitute known and dependend variables
  let e = subst (flip M.lookup lin) (lhs - rhs)
      in addEq0 deps e

addEqs :: (Hashable v, RealFrac (Phase n), Ord v, Floating n) => Dependencies v n -> [Expr v n] -> Either (DepError n) (Dependencies v n)
addEqs = foldM addEq0

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
  
addEq0 :: (Hashable v, RealFrac (Phase n), Ord v, Floating n) => Dependencies v n -> Expr v n -> Either (DepError n) (Dependencies v n)
-- adding a constant equation
addEq0 _  e
  | Just c <- getConstExpr e =
      if c == 0 then Left RedundantEq
      else Left (InconsistentEq c)

-- adding a linear equation
addEq0 (Dependencies vdep lin trig nonlin) (Expr lt [] []) =
  let (v, lt2) = splitMax lt
      -- variables that depend on v
      depVars = fromMaybe H.empty (M.lookup v vdep)
      -- substitute v in all dependend variables
      -- and add v as dependend variable
      lin' = M.insert v lt2 $
             H.foldl' (flip $ M.adjust $ substVarLin $
                       simpleSubst v lt2) lin depVars
      -- independend variables substituted
      ltVars = case lt2 of
        LinTerm _ vars -> map fst vars
      -- add dependency link from independend variables to the
      -- substituted equations and v, and remove v (since it has
      -- become dependend, so no variable can depend on it).
      depVars2 = H.insert v depVars
      vdep' = H.foldl'
              (\mp k -> M.insertWith H.union k depVars2 mp)
              (M.delete v vdep) (H.fromList ltVars)
      -- simply substitute var in nonlinear eqs
      nonlin' = map (subst (simpleSubst v lt2)) nonlin
      -- find trigonometric equation containing var
      (hasDep, trig') = partition trigDepends trig
      trigDepends (p, LinTerm _ a,_,_) =
        any ((==v).fst) p || any ((==v).fst) a
      -- substitute and evaluate trigonometric equations
      trigSubst (p, a, ph, c) =
        subst (simpleSubst v lt2) $
        (sin $ linExpr $ LinTerm ph p) *
        linExpr a + makeConstant c
      newTrig = map trigSubst hasDep
  in addEqs (Dependencies vdep' lin' trig' []) (newTrig++nonlin')

-- reduce a sine to linear equation
addEq0 deps (Expr (LinTerm c []) [(theta, [(alpha, LinTerm n [])])] []) =
  addEq0 deps (linExpr (LinTerm (alpha - (asin $ -c/n)) theta))

--  adding the first sine equation
addEq0 (Dependencies d lin [] nl) (Expr (LinTerm c []) [(theta, [(alpha, n)])] []) =
  Right $ Dependencies d lin [(theta, n, alpha, c)] nl

-- try reducing this equation with another sine equation
addEq0 (Dependencies deps lin trig nl)
  (Expr (LinTerm x []) [(theta, [(a, n)])] []) =
  case mapMaybe similarTrig $ select trig of
   -- no matching equation found
   [] -> Right $ Dependencies deps lin ((theta, n, a, x):trig) nl
   -- solve for angle and amplitude, and add resulting linear
   -- equations
   l -> addEqs (Dependencies deps lin rest nl) [lin1, lin2]
     where
       ((b,y), rest) = maximumBy (maxTrig `on` fst) l
       maxTrig (t1,_) (t2,_) = 
         compare ((t1-a)`dmod`pi) ((t2-a)`dmod`pi)
       d      = sin(a-b)
       e      = y*cos(a-b)-x
       theta2 = atan (-y*d/e)-b +
                (if (d*e) < 0 then pi else 0)
       n2     = sqrt(y*y + e*e/(d*d))
       lin1   = linExpr $ LinTerm (-theta2) theta
       lin2   = linExpr n - makeConstant n2
  where
    similarTrig ((t,m,b,y),rest)
      | Just r <- termIsMultiple m n,
        t == theta &&
        (b-a) `dmod` pi > pi/8 =
          Just ((b,y/r),rest)
      | otherwise = Nothing

-- just add any other equation to the list of nonlinear equations
addEq0 (Dependencies d lin trig nonlin) e =
  Right $ Dependencies d lin trig (e:nonlin)

dmod :: RealFrac a => a -> a -> a
dmod a b = abs((a/b) - fromInteger (round (a/b)) * b)

-- put the variable with the maximum coefficient on the lhs of the
-- equation
splitMax :: (Ord b, Fractional b, Eq v) => LinTerm v b -> (v, LinTerm v b)
splitMax (LinTerm c t) =
  let (v,c2) = maximumBy (compare `on` (abs.snd)) t
  in (v, LinTerm (-c/c2) $
         map (fmap (negate.(/c2))) $
         filter ((/= v).fst) t)
      
-- | Return True if the variable is known or dependend.
varDefined :: (Eq v, Hashable v) => Dependencies v n -> v -> Bool
varDefined (Dependencies _ dep _ _) v =
  case M.lookup v dep of
    Nothing -> False
    _ -> True

-- -- | Return all dependend variables with their dependencies.
-- dependendVars :: Dependencies n v -> [(v, LinTerm v n)]
-- dependendVars (Dependencies dep) = filter (not.known.snd) $ M.toList dep

-- | Return all known variables.
knownVars :: Dependencies v n -> [(v, n)]
knownVars (Dependencies _ lin _ _) =
  mapMaybe knownVar $ M.toList lin
  where
    knownVar (v, LinTerm n []) = Just (v, n)
    knownVar _ = Nothing

-- -- | Return all independend variables.
-- freeVars :: (Eq v, Hashable v) => Dependencies n v -> [v]
-- freeVars (Dependencies dep) =
--   HS.toList $ M.foldl' addVars HS.empty dep
--   where addVars s (LinTerm _ a) =
--           HS.union s $ HS.fromList $ map fst a

-- | Return the value of the variable, or a list of variables
-- it depends on.  Only linear dependencies are shown.
getKnown :: (Eq v, Hashable v) => Dependencies v n -> v -> Either [v] n
getKnown (Dependencies _ lin _ _) var =
  case M.lookup var lin of
    Nothing -> Left  []
    Just (LinTerm a []) ->
      Right a
    Just (LinTerm _ v) ->
      Left $ map fst v

trigToExpr :: (Ord n, Ord v, Floating n) => TrigEq v n -> Expr v n
trigToExpr (p, a, ph, c) =
  linExpr a * sin(linExpr $ LinTerm ph p) +
  makeConstant c

-- | Give all nonlinear equations as an `Expr` equal to 0.
nonlinearEqs :: (Ord n, Ord v, Floating n) => Dependencies v n -> [Expr v n]
nonlinearEqs  (Dependencies _ _ trig nl) =
  map trigToExpr trig ++ nl
  
-- | Make the pairs of expressions on both sides equal, and add the
-- result to the Set of dependencies.  No error is signaled if the
-- equation for one of the sides is redundant for example in (x, 0) ==
-- (y, 0).
(=&=) :: (Hashable v, RealFrac (Phase n), Ord v, Floating n) => (Expr v n, Expr v n) -> (Expr v n, Expr v n) -> Dependencies v n -> Either (DepError n) (Dependencies v n)
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
solveEq :: (Dependencies v n) -> [Dependencies v n -> Either (DepError n) (Dependencies v n)] -> Either (DepError n) (Dependencies v n)
solveEq = foldM $ flip ($)

-- | Show all variables and equations.
showVars :: (Show n, Show v, Show a, Ord n, Ord v, Floating n) => Either (DepError a) (Dependencies v n) -> IO ()
showVars (Left e) = putStrLn $ case e of
  InconsistentEq a -> "Inconsistent equations, off by " ++ show a
  RedundantEq -> "Redundant Equation."
showVars (Right dep) = putStrLn $ show dep
