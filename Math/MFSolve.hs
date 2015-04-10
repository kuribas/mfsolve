{-# LANGUAGE DeriveGeneric, PatternGuards #-}

{-|
Module      : Math.MFSolve
Description : solving linear equations in an iterative way, à la metafont.
Copyright   : (c) Kristof Bastiaensen, 2014
License     : BSD-3
Maintainer  : kristof@resonata.be
Stability   : unstable
Portability : portable

This module solves linear equations in an iterative way, like in
metafont, but extended with a solver for angles, and making the order
or the equation independent.

The solver solves linear equations and evaluates non-linear
expressions on the fly.  It can also solve for angles from sines and
cosines.

For example:

>--Turn the given strings into variables.
>[a, b, c, d] = map makeVariable ["a", "b", "c", "d"]
>
>test = showVars $ solveEq emptyDeps [
>  a === 0.8*b + 0.2*c,
>  d === pi/2,
>  b+a === sin(d),
>  c === d
>]

  Returns:

>"d" = 1.5707963267948966
>"a" = 0.6189773696438774
>"b" = 0.3810226303561226
>"c" = 1.5707963267948966
-}

module Math.MFSolve
--        (Dependencies, DependencyList(..), DepError(..), DependendExpr,
                     -- emptyDeps, addEquation, makeVariable, makeConstant,
                     -- (===), (=&=), solveEq, getKnown, showVars, freeVars, dependendVars,
                     -- varDefined, knownVars)
where
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as HS
import GHC.Generics
import Data.Hashable
import Data.List
import Data.Maybe
import Control.Monad

--  | _labeled_ black box mathematical functions
data UnaryFun n = UnaryFun UnaryOp (n -> n)

data BinaryOp = Add | Mul
data UnaryOp =
  Sin | Abs | Recip | Signum |
  Exp | Log | Cos | Cosh | Atanh |
  Tan | Sinh | Asin | Acos | Asinh | Acosh | Atan

data SimpleExpr v n =
  SEBin BinaryOp (SimpleExpr v n) (SimpleExpr v n) |
  SEUn UnaryOp (SimpleExpr v n) |
  Var v |
  Const n

-- | generic expression
data Expr v n = Expr (LinTerm v n) [TrigTerm v n] [NonLinTerm v n]

-- A linear term of several variables.
-- For example: @2*a + 3*b + 2@ would be represented as
-- @DependencyList 2 [(a, 2), (b, 3)]@.
data LinTerm v n = LinTerm n [(v, n)]
                 deriving Generic
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

-- | An angular function of the form @c + v*sin(terms + phi)@
-- where @terms@, and @v@ are linear terms, @phi@ and @c@ are constants.
data AngularDeps v n = AngularDeps n (LinTerm v n) (LinTerm v n)

type LinearMap v n = M.HashMap v (LinTerm v n)
type AngularMap v n = M.HashMap (LinTerm v n, LinTerm v n) (AngularDeps v n)

instance (Hashable v, Hashable n) => Hashable (LinTerm v n)

-- | An opaque datatype containing the dependencies of each variable.
-- A variable who's dependency is just a number is called /known/.  A
-- variables which depends on other variables is called
-- /dependend/.  A variable which is neither known or dependend is
-- called /independend/.  A variable can only depend on other /independend/ variables.
data Dependencies v n = Dependencies (LinearMap v n) (AngularMap v n) [Expr v n]

-- | An error type for '===', '=&=', 'solveEq' and 'addEquation':
data DepError n =
  -- | 'InconsistentEq' @a@: The equation was reduced to the
  -- impossible equation `a == 0` for nonzero a, which means the
  -- equation is inconsistent with previous equations.
  InconsistentEq n |
  -- | 'RedundantEq': The equation was reduced to the redundant equation 0 == 0, which
  -- means it doesn't add any information.
  RedundantEq

instance (Show n, Num n, Eq n, Show v) => Show (LinTerm v n) where
  show (LinTerm a b) =
    concat $ intersperse " + " (show a: map showPair b)
      where showPair (c, 1) = show c
            showPair (c, d) = show c ++ " " ++ show d

zeroTerm :: (Num n) => LinTerm v n
zeroTerm = LinTerm 0 []

linExpr :: LinTerm v n -> Expr v n
linExpr lt = Expr lt [] []

makeConstant :: n -> Expr v n
makeConstant c = linExpr (LinTerm c [])

makeVariable :: Num n => v -> Expr v n
makeVariable v = linExpr (LinTerm 0 [(v, 1)])

trigExpr :: (Num n) => [TrigTerm v n] -> Expr v n
trigExpr t = Expr zeroTerm t []

nonlinExpr :: Num n => [NonLinTerm v n] -> Expr v n
nonlinExpr n = Expr zeroTerm [] n

zeroExpr :: (Num n) => Expr v n
zeroExpr = Expr zeroTerm [] []

isZeroTerm :: (Num t1, Eq t1) => LinTerm t t1 -> Bool
isZeroTerm (LinTerm 0 []) = True
isZeroTerm _ = False

getConst :: LinTerm t a -> Maybe a
getConst (LinTerm a []) = Just a
getConst _ = Nothing

getLin :: Expr t n -> Maybe (LinTerm t n)
getLin (Expr lt [] []) = Just lt
getLin _ = Nothing

getConstExpr :: Expr t b -> Maybe b
getConstExpr e = getLin e >>= getConst

getTrig :: (Num n, Eq n) => Expr t n -> Maybe [TrigTerm t n]
getTrig (Expr _ [] _) = Nothing
getTrig (Expr lt trig [])
  | isZeroTerm lt = Just trig
  | otherwise = Nothing
getTrig _ = Nothing

addLin :: (Ord v, Num n, Eq n) => LinTerm v n -> LinTerm v n -> LinTerm v n
addLin (LinTerm c1 terms1) (LinTerm c2 terms2) =
  LinTerm (c1+c2) terms3 where
    terms3 = filter ((/= 0) . snd) $
             merge terms1 terms2 (+)

addExpr :: (Ord n, Ord v, Num n, RealFloat n) => Expr v n -> Expr v n -> Expr v n
addExpr (Expr lt1 trig1 nl1) (Expr lt2 trig2 nl2) =
  Expr (addLin lt1 lt2) trig3 (nl1++nl2)
  where
    trig3 = merge trig1 trig2 addTrigTerms

-- -- | An empty set of dependencies.
-- emptyDeps :: Dependencies v n
-- emptyDeps = Dependencies M.empty M.empty []

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
addTrigTerms :: (Ord t, RealFloat t1) => [(t1, LinTerm t t1)] -> [(t1, LinTerm t t1)] -> [(t1, LinTerm t t1)]
addTrigTerms [] p = p
addTrigTerms terms terms2 =
  foldr mergeTerms terms terms2
  where
    mergeTerms (alpha, n) ((beta, m):rest) =
      case addTrigTerm alpha n beta m of
       Just (gamma, o) -> mergeTerms (gamma, o) rest
       Nothing -> (beta, m) : mergeTerms (alpha, n) rest
    mergeTerms a [] = [a]

-- ratio*c2, 1*c2

addTrigTerm :: (RealFloat a, Ord v, Num a, Ord a) => a -> LinTerm v a -> a -> LinTerm v a -> Maybe (a, LinTerm v a)
addTrigTerm alpha n beta m
  | alpha == beta =
    Just (alpha, addLin n m)
  | Just r <- termIsMultiple n m =
      let gamma = atan2 divident divisor +
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
termIsMultiple (LinTerm c1 r1@((_, d1):_)) (LinTerm c2 r2@((_, d2):_))
  | c1 == 0 && c2 == 0 && compareBy r1 r2 (compareTerm (d1/d2)) =
      Just (d1/d2)
  | compareBy r1 r2 (compareTerm (c1/c2)) =
      Just (c1/c2)
  | otherwise = Nothing
  where
    compareTerm ratio (v3,c3) (v4, c4) = 
      v3 == v4 && (abs(c3 - (c4 * ratio)) < c3*(2e-50))
termIsMultiple _ _ = Nothing

compareBy :: [a] -> [b] -> (a -> b -> Bool) -> Bool
compareBy [] [] _ = True
compareBy (e:l) (e2:l2) f =
  f e e2 && compareBy l l2 f
compareBy _ _ _ = False
        
-- multiply a dependencylist by a value.
mulLinTerm :: (Ord n, Num n) =>
            n -> LinTerm v n -> LinTerm v n
mulLinTerm x (LinTerm e terms) =
  LinTerm (e*x) $ map (fmap (*x)) terms

-- multiply all sines with the linear expression
mulTrig :: (Ord n, RealFloat n, Ord v) => LinTerm v n -> (Period v n, [(Phase n, LinTerm v n)]) -> Expr v n
mulTrig (LinTerm c []) (theta, terms) =
  -- constant multiplier
  trigExpr [(theta, tt)] where
    tt = map (fmap (mulLinTerm c)) terms
mulTrig lt (theta, terms) =
  -- linear multiplier
  foldr (+) zeroExpr (map mul1 terms)
  where
    -- constant amplitude
    mul1 (alpha, LinTerm c []) =
      trigExpr [(theta, [(alpha, mulLinTerm c lt)])]
    -- linear amplitude
    mul1 t =
      nonlinExpr [MulExp (trigExpr [(theta, [t])])
                      (Expr lt [] [])]

-- linear * linear
mulExpr :: (Ord n, RealFloat n, Ord t) => Expr t n -> Expr t n -> Expr t n
mulExpr e1@(Expr lt1 [] []) e2@(Expr lt2 [] [])
  | Just c <- getConst lt1 =
      Expr (mulLinTerm c lt2) [] []
  | Just c <- getConst lt2 =
      Expr (mulLinTerm c lt1) [] []
  | otherwise = nonlinExpr [MulExp e1 e2]
-- linear * trig
mulExpr (Expr lt [] []) e2 
  | Just trig <- getTrig e2 =
      foldr ((+).mulTrig lt) zeroExpr trig
-- trig * linear      
mulExpr e1 (Expr lt [] [])
  | Just trig <- getTrig e1 =
      foldr ((+).mulTrig lt) zeroExpr trig
-- anything else
mulExpr e1 e2 = nonlinExpr [MulExp e1 e2]
      
sinExpr :: Num n => Expr v n -> Expr v n
sinExpr (Expr (LinTerm c t) [] []) =
  trigExpr [(t, [(c, LinTerm 1 [])])]
sinExpr e = nonlinExpr [SinExp e]

unExpr :: Num n => UnaryFun n -> Expr v n -> Expr v n
unExpr (UnaryFun _ f) e
  | Just c <- getConstExpr e =
      makeConstant (f c)
unExpr f e = nonlinExpr [UnaryApp f e]

substVarLin :: (RealFloat n, Ord n, Ord v) => v -> Expr v n -> LinTerm v n -> Expr v n
substVarLin v e dep@(LinTerm a terms) =
  case lookup v terms of
   Nothing -> linExpr dep
   Just b ->
     makeConstant b * e +
     (linExpr $ LinTerm a $
      filter ((/= v) . fst) terms)


substVarNonLin :: (RealFloat n, Ord n, Ord v) => v -> Expr v n -> NonLinTerm v n -> Expr v n
substVarNonLin v e (UnaryApp f e1) =
  unExpr f (substVar v e e1)
substVarNonLin v e (MulExp e1 e2) =
  mulExpr (substVar v e e1) (substVar v e e2)
substVarNonLin v e (SinExp e1) =
  sinExpr (substVar v e e1)

substVarTrig :: (RealFloat n, Ord n, Ord v) => v -> Expr v n -> ([(v, n)], [(n, LinTerm v n)]) -> Expr v n
substVarTrig v e (period, terms) =
  let period2 = substVarLin v e (LinTerm 0 period)
      terms2 = map (fmap $ substVarLin v e) terms
  in foldr (\(p,a) -> (+ (a * sin (makeConstant p + period2))))
     zeroExpr terms2

substVar :: (RealFloat n, Num n, Ord v) => v -> Expr v n -> Expr v n -> Expr v n
substVar v e (Expr lt trig nl) =
  substVarLin v e lt +
  foldr ((+).substVarTrig v e) zeroExpr trig +
  foldr ((+).substVarNonLin v e) zeroExpr nl

instance (RealFloat n, Ord v) => Num (Expr v n) where
  (+) = addExpr
  (*) = mulExpr
  negate = mulExpr (-1)
  abs = unExpr (UnaryFun Abs abs)
  signum = unExpr (UnaryFun Signum signum)
  fromInteger = makeConstant . fromInteger

instance (RealFloat n, Ord v) => Fractional (Expr v n) where
   recip = unExpr (UnaryFun Recip (1.0/))
   fromRational = makeConstant . fromRational

instance (RealFloat n, Ord v) => Floating (Expr v n) where
  pi = makeConstant pi
  exp = unExpr (UnaryFun Exp exp)
  log = unExpr (UnaryFun Log log)
  sin = sinExpr
  cos a = sinExpr (a + pi/2)
  cosh = unExpr (UnaryFun Cosh cosh)
  atanh = unExpr (UnaryFun Atanh atanh)
  tan = unExpr (UnaryFun Tan tan)
  sinh = unExpr (UnaryFun Sinh sinh)
  asin = unExpr (UnaryFun Asin asin)
  acos = unExpr (UnaryFun Acos acos)
  asinh = unExpr (UnaryFun Asinh asinh)
  acosh = unExpr (UnaryFun Acosh acosh)
  atan = unExpr (UnaryFun Atan atan)


-- -- -- substitute all known and dependend variables in the list
-- substAll :: (Num n, Ord n, Ord v, Hashable v) =>
--             LinTerm v n -> Dependencies v n -> LinTerm v n
-- substAll dl@(LinTerm _ vars) (Dependencies dep _ _) =
--   let substOne d v = case M.lookup v dep of
--         Just dv -> substVarLin v dv d
--         Nothing -> d
--   in foldl substOne dl (map fst vars)

-- -- -- add two dependency lists
-- addDL :: (Ord n, Num n, Ord v, Hashable v) =>
--          Dependencies v n -> LinTerm v n -> LinTerm v n -> LinTerm v n
-- addDL dep dl1 dl2 =
--   let LinTerm e v = substAll dl1 dep
--       LinTerm f w = substAll dl2 dep
--   in LinTerm (e+f) $ filter ((/= 0) . snd) $ merge v w (+)

-- -- -- | Add an equation to the set of dependencies, and return a new set
-- -- -- or signal an error.
-- addEquation :: (Ord v, Ord n, Fractional n, Hashable v) =>
--                LinTerm v n -> LinTerm v n -> Dependencies v n
--             -> Either (DepError n) (Dependencies v n)
-- addEquation lhs rhs deps@(Dependencies depend _ _) =
--   let LinTerm e v = addDL deps rhs $ mulLinTerm (-1) lhs
--   in case v of
--     -- no variables left
--     [] -> Left $ if e == 0 then RedundantEq else InconsistentEq e

--     -- independend variable
--     ((v1,c1):vs) -> let
--       f = negate e / c1
--       w = map (fmap (/ negate c1)) vs
--       dl = LinTerm f w
--       in Right $ Dependencies (M.insert v1 dl $ M.map (substVarLin v1 dl) depend) undefined undefined

-- infixr 1 ===, =&=

-- known :: LinTerm v n -> Bool
-- known (LinTerm _ []) = True
-- known (LinTerm _ _) = False

-- -- | Return True if the variable is known or dependend.
-- varDefined :: (Eq v, Hashable v) => Dependencies n v -> v -> Bool
-- varDefined (Dependencies dep) v =
--   case M.lookup v dep of
--     Nothing -> False
--     _ -> True

-- -- | Return all dependend variables with their dependencies.
-- dependendVars :: Dependencies n v -> [(v, LinTerm v n)]
-- dependendVars (Dependencies dep) = filter (not.known.snd) $ M.toList dep

-- -- | Return all known variables.
-- knownVars :: Dependencies n v -> [(v, n)]
-- knownVars (Dependencies dep) = mapMaybe knownVar $ M.toList dep
--   where
--     knownVar (v, LinTerm n []) = Just (v, n)
--     knownVar _ = Nothing

-- -- | Return all independend variables.
-- freeVars :: (Eq v, Hashable v) => Dependencies n v -> [v]
-- freeVars (Dependencies dep) =
--   HS.toList $ M.foldl' addVars HS.empty dep
--   where addVars s (LinTerm _ a) =
--           HS.union s $ HS.fromList $ map fst a

-- -- | Return the value of the variable, or a list of variables
-- -- it depends on.
-- getKnown :: (Eq v, Hashable v) => Dependencies n v -> v -> Either [v] n
-- getKnown (Dependencies dep) var =
--   case M.lookup var dep of
--     Nothing -> Left  []
--     Just (LinTerm a []) ->
--       Right a
--     Just (LinTerm _ v) ->
--       Left $ map fst v
  
-- -- | Make the expressions on both sides equal, and add the result to the Set of
-- -- dependencies.
-- (===) :: (Ord v, Ord n, Show n, Fractional n, Show v, Hashable v) =>
--          DependendExpr n v -> DependendExpr n v -> Dependencies n v
--       -> Either (DepError n v) (Dependencies n v)
-- (===) a b dep = do
--   dlA <- calcDL a dep
--   dlB <- calcDL b dep
--   addEquation dlA dlB dep

-- -- | Make the pairs of expressions on both sides equal, and add the result to the Set of
-- -- dependencies.  No error is signaled if the equation for one of the sides is redundant
-- -- for example in (x, 0) == (y, 0).
-- (=&=) :: (Fractional n, Ord n, Ord v, Show n, Show v, Hashable v) =>
--          (DependendExpr n v, DependendExpr n v)
--       -> (DependendExpr n v, DependendExpr n v)
--       -> Dependencies n v -> Either (DepError n v) (Dependencies n v)
-- (=&=) (a, b) (c, d) dep = 
--   case (a === c) dep of
--     Left RedundantEq ->
--       (b === d) dep
--     Right res ->
--       case (b === d) res of
--         Left RedundantEq -> Right res
--         Right res2 -> Right res2
--         err -> err
--     err -> err

-- -- | Solve a list of equations in order.  Returns either a new set of dependencies, or signals an error.
-- --solveEq l = solveEq' l emptyDeps
-- solveEq :: (Dependencies n v) -> [Dependencies n v -> Either (DepError n v) (Dependencies n v)] -> Either (DepError n v) (Dependencies n v)
-- solveEq = foldM (flip ($))

-- -- | Show the dependencies of all variables.
-- showVars :: (Show n, Show v) =>
--             Either (DepError n v) (Dependencies n v) -> IO ()
-- showVars (Left e) = putStrLn $ case e of
--   InconsistentEq a -> "Inconsistent equations, off by " ++ show a
--   RedundantEq -> "Redundant Equation."
--   UnknownUnary f _ -> "Cannot take the " ++ f ++ " of an unknown value"
--   UnknownBinary "mul" _ -> "Cannot multiply two unknown values"
--   UnknownBinary "exp" _ -> "Cannot raise to an unknown value"
--   UnknownBinary _ _ -> error "showVars: internal error."
-- showVars (Right (Dependencies dep)) = do
--   mapM_ showIt $ M.toList dep
--     where showIt (v, e) = putStrLn (show v ++ " = " ++ show e)

