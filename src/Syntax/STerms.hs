module Syntax.STerms
  ( module Syntax.CommonTerm
  , XtorArgs(..)
  , SCase(..)
  , STerm(..)
  , Command(..)
    -- Variable Opening
  , commandOpening
  , commandOpeningSingle
    -- Variable Closing
  , commandClosing
  , commandClosingSingle
  -- Locally Closed Check
  , termLocallyClosed
  , commandLocallyClosed
  , checkIfBound
  -- Free Variables
  , isClosed_term
  -- Transform to named representation for prettyprinting
  , openSTermComplete
  , openCommandComplete
  ) where

import Data.Containers.ListUtils (nubOrd)
import Data.List (elemIndex)
import Data.Maybe (fromJust, isJust)

import Utils
import Syntax.CommonTerm

---------------------------------------------------------------------------------
-- # Symmetric Terms
--
-- Symmetric terms are called symmetric for two reasons:
-- 1.) They treat producers and consumers of a type as equally first class. This
-- is in distinction to asymmetric terms, which only have a first class representation
-- for producers.
-- 2.) The "producer" and "consumer" terms are completely isomorphic, and therefore
-- represented using one representation `STerm` which is parameterized by a `PrdCns` tag.
--
-- The correspondence between asymmetric and symmetric terms is therefore:
--
--          ATerm    <->  Producer  = STerm Prd
--                        Consumer  = STerm Cns
--
--
-- ## Variable representation
--
-- We use the locally nameless representation for terms, which combines names for
-- free variables with  anonymous deBruijn indexes for bound variables.
-- The locally namelesss representation is well documented here:
-- https://www.chargueraud.org/softs/ln/
---------------------------------------------------------------------------------

-- | Represents an argument list to a constructor or destructor.
data XtorArgs a = MkXtorArgs { prdArgs :: [STerm Prd a]
                             , cnsArgs :: [STerm Cns a]
                             }
                  deriving (Show, Eq)

-- | Represents one case in a pattern match or copattern match.
--
--        X(x_1,...,x_n)[k_1,...,k_m] => c
--        ^ ^^^^^^^^^^^^^^^^^^^^^^^^     ^
--        |              |               |
--    scase_name     scase_args      scase_cmd
--
data SCase a = MkSCase
  { scase_name :: XtorName
  , scase_args :: Twice [a]
  , scase_cmd  :: Command a
  } deriving (Show, Eq)


-- | A symmetric term.
-- The `bs` parameter is used to store additional information at binding sites.
data STerm (pc :: PrdCns) bs where
  -- | A bound variable in the locally nameless system.
  BoundVar :: PrdCnsRep pc -> Index -> STerm pc bs
  -- | A free variable in the locally nameless system.
  FreeVar  :: PrdCnsRep pc -> FreeVarName -> STerm pc bs
  -- | A constructor or destructor.
  -- If the first argument is `PrdRep` it is a constructor, a destructor otherwise.
  XtorCall :: PrdCnsRep pc -> XtorName -> XtorArgs bs -> STerm pc bs
  -- | A pattern or copattern match.
  -- If the first argument is `PrdRep` it is a copattern match, a pattern match otherwise.
  XMatch   :: PrdCnsRep pc -> NominalStructural -> [SCase bs] -> STerm pc bs
  -- | A Mu or TildeMu abstraction:
  --
  --  mu k.c    =   MuAbs PrdRep c
  -- ~mu x.c    =   MuAbs CnsRep c

  MuAbs    :: PrdCnsRep pc -> a -> Command a -> STerm pc a
  deriving (Eq)
deriving instance Show a => Show (STerm pc a)


---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------

-- | An executable command.
data Command bs
  -- | A producer applied to a consumer:
  --
  --   p >> c
  = Apply (STerm Prd bs) (STerm Cns bs)
  | Print (STerm Prd bs)
  | Done
  deriving (Show, Eq)

---------------------------------------------------------------------------------
-- Variable Opening
---------------------------------------------------------------------------------

termOpeningRec :: Int -> XtorArgs bs -> STerm pc bs -> STerm pc bs
termOpeningRec k MkXtorArgs { prdArgs } bv@(BoundVar PrdRep (i,j)) | i == k    = prdArgs !! j
                                                                   | otherwise = bv
termOpeningRec k MkXtorArgs { cnsArgs } bv@(BoundVar CnsRep (i,j)) | i == k    = cnsArgs !! j
                                                                   | otherwise = bv
termOpeningRec _ _ fv@(FreeVar _ _)       = fv
termOpeningRec k args (XtorCall s xt (MkXtorArgs prdArgs cnsArgs)) =
  XtorCall s xt (MkXtorArgs (termOpeningRec k args <$> prdArgs)
                            (termOpeningRec k args <$> cnsArgs))
termOpeningRec k args (XMatch pc sn cases) =
  XMatch pc sn $ map (\pmcase@MkSCase{ scase_cmd } -> pmcase { scase_cmd = commandOpeningRec (k+1) args scase_cmd }) cases
termOpeningRec k args (MuAbs pc a cmd) =
  MuAbs pc a (commandOpeningRec (k+1) args cmd)

commandOpeningRec :: Int -> XtorArgs bs -> Command bs -> Command bs
commandOpeningRec _ _ Done = Done
commandOpeningRec k args (Print t) = Print (termOpeningRec k args t)
commandOpeningRec k args (Apply t1 t2) = Apply (termOpeningRec k args t1) (termOpeningRec k args t2)


-- replaces bound variables pointing "outside" of a command with given arguments
commandOpening :: XtorArgs a -> Command a -> Command a
commandOpening = commandOpeningRec 0

commandOpeningSingle :: PrdCnsRep pc -> STerm pc a -> Command a -> Command a
commandOpeningSingle PrdRep t = commandOpening (MkXtorArgs [t] [])
commandOpeningSingle CnsRep t = commandOpening (MkXtorArgs [] [t])

---------------------------------------------------------------------------------
-- Variable Closing
---------------------------------------------------------------------------------

termClosingRec :: Int -> Twice [FreeVarName] -> STerm pc a -> STerm pc a
termClosingRec _ _ bv@(BoundVar _ _) = bv
termClosingRec k (Twice prdvars _) (FreeVar PrdRep v) | isJust (v `elemIndex` prdvars) = BoundVar PrdRep (k, fromJust (v `elemIndex` prdvars))
                                                      | otherwise = FreeVar PrdRep v
termClosingRec k (Twice _ cnsvars) (FreeVar CnsRep v) | isJust (v `elemIndex` cnsvars) = BoundVar CnsRep (k, fromJust (v `elemIndex` cnsvars))
                                                      | otherwise = FreeVar CnsRep v
termClosingRec k vars (XtorCall s xt (MkXtorArgs prdArgs cnsArgs)) =
  XtorCall s xt (MkXtorArgs (termClosingRec k vars <$> prdArgs)(termClosingRec k vars <$> cnsArgs))
termClosingRec k vars (XMatch pc sn cases) =
  XMatch pc sn $ map (\pmcase@MkSCase { scase_cmd } -> pmcase { scase_cmd = commandClosingRec (k+1) vars scase_cmd }) cases
termClosingRec k vars (MuAbs pc a cmd) =
  MuAbs pc a (commandClosingRec (k+1) vars cmd)

commandClosingRec :: Int -> Twice [FreeVarName] -> Command a -> Command a
commandClosingRec _ _ Done = Done
commandClosingRec k args (Print t) = Print (termClosingRec k args t)
commandClosingRec k args (Apply t1 t2) = Apply (termClosingRec k args t1) (termClosingRec k args t2)

commandClosing :: Twice [FreeVarName] -> Command a -> Command a
commandClosing = commandClosingRec 0

commandClosingSingle :: PrdCnsRep pc -> FreeVarName -> Command a -> Command a
commandClosingSingle PrdRep v = commandClosing (Twice [v] [])
commandClosingSingle CnsRep v = commandClosing (Twice [] [v])


---------------------------------------------------------------------------------
-- Check for locally closedness
---------------------------------------------------------------------------------

checkIfBound :: [Twice [a]] -> PrdCnsRep pc -> Index -> Either Error ()
checkIfBound env rep  (i, j) | i >= length env = Left $ OtherError "Variable is not bound"
                             | otherwise = checkIfBound' (env !! i) rep j

checkIfBound' :: Twice [a] -> PrdCnsRep pc -> Int -> Either Error ()
checkIfBound' (Twice prds _) PrdRep j = if j < length prds then Right () else Left $ OtherError "Variable is not bound"
checkIfBound' (Twice _ cnss) CnsRep j = if j < length cnss then Right () else Left $ OtherError "Variable is not bound"

termLocallyClosedRec :: [Twice [()]] -> STerm pc a -> Either Error ()
termLocallyClosedRec env (BoundVar pc idx) = checkIfBound env pc idx
termLocallyClosedRec _ (FreeVar _ _) = Right ()
termLocallyClosedRec env (XtorCall _ _ (MkXtorArgs prds cnss)) = do
  sequence_ (termLocallyClosedRec env <$> prds)
  sequence_ (termLocallyClosedRec env <$> cnss)
termLocallyClosedRec env (XMatch _ _ cases) = do
  sequence_ ((\MkSCase { scase_cmd, scase_args } -> commandLocallyClosedRec (twiceMap (fmap (const ())) (fmap (const ())) scase_args : env) scase_cmd) <$> cases)
termLocallyClosedRec env (MuAbs PrdRep _ cmd) = commandLocallyClosedRec (Twice [] [()] : env) cmd
termLocallyClosedRec env (MuAbs CnsRep _ cmd) = commandLocallyClosedRec (Twice [()] [] : env) cmd

commandLocallyClosedRec :: [Twice [()]] -> Command a -> Either Error ()
commandLocallyClosedRec _ Done = Right ()
commandLocallyClosedRec env (Print t) = termLocallyClosedRec env t
commandLocallyClosedRec env (Apply t1 t2) = termLocallyClosedRec env t1 >> termLocallyClosedRec env t2

termLocallyClosed :: STerm pc a -> Either Error ()
termLocallyClosed = termLocallyClosedRec []

commandLocallyClosed :: Command a -> Either Error ()
commandLocallyClosed = commandLocallyClosedRec []

---------------------------------------------------------------------------------
-- Compute set of free variables and check if term is closed
---------------------------------------------------------------------------------

combineFreeVars :: [Twice[FreeVarName]] -> Twice [FreeVarName]
combineFreeVars = foldr combineFreeVars' (Twice [] [])
  where
    combineFreeVars' :: Twice [FreeVarName] -> Twice [FreeVarName] -> Twice [FreeVarName]
    combineFreeVars' (Twice prds1 cnss1) (Twice prds2 cnss2) = Twice (nubOrd (prds1 ++ prds2)) (nubOrd (cnss1 ++ cnss2))

freeVars_term :: STerm pc a -> Twice [FreeVarName]
freeVars_term (BoundVar _ _) = Twice [] []
freeVars_term (FreeVar PrdRep v) = Twice [v] []
freeVars_term (FreeVar CnsRep v) = Twice [] [v]
freeVars_term (XtorCall _ _ (MkXtorArgs prds cnss)) = combineFreeVars (map freeVars_term prds ++ map freeVars_term cnss)
freeVars_term (XMatch _ _ cases)                  = combineFreeVars (map (\MkSCase { scase_cmd } -> freeVars_cmd scase_cmd) cases)
freeVars_term (MuAbs _ _ cmd)                  = freeVars_cmd cmd

freeVars_cmd :: Command a -> Twice [FreeVarName]
freeVars_cmd (Apply t1 t2) = combineFreeVars [freeVars_term t1, freeVars_term t2]
freeVars_cmd _             = Twice [] []

-- tests if a term is closed, i.e. contains no free variables
isClosed_term :: STerm Prd a -> Bool
isClosed_term t = freeVars_term t == Twice [] []

---------------------------------------------------------------------------------
-- These functions  translate a locally nameless term into a named representation.
--
-- Use only for prettyprinting! These functions only "undo" the steps in the parser
-- and do not fulfil any semantic properties w.r.t shadowing etc.!
---------------------------------------------------------------------------------

openXtorArgsComplete :: XtorArgs FreeVarName -> XtorArgs FreeVarName
openXtorArgsComplete (MkXtorArgs prdArgs cnsArgs) =
  MkXtorArgs (openSTermComplete <$> prdArgs) (openSTermComplete <$> cnsArgs)

freeVarNamesToXtorArgs :: Twice [FreeVarName] -> XtorArgs FreeVarName
freeVarNamesToXtorArgs (Twice prds cnss) = MkXtorArgs ((\n -> FreeVar PrdRep n) <$> prds) ((\n -> FreeVar CnsRep n) <$> cnss)

openSTermComplete :: STerm pc FreeVarName -> STerm pc FreeVarName
openSTermComplete (BoundVar pc idx) = BoundVar pc idx
openSTermComplete (FreeVar pc v) = FreeVar pc v
openSTermComplete (XtorCall pc name args) = XtorCall pc name (openXtorArgsComplete args)
openSTermComplete (XMatch pc ns cases) = let
  openSCase :: SCase FreeVarName -> SCase FreeVarName
  openSCase MkSCase { scase_name, scase_args, scase_cmd } =
    MkSCase { scase_name = scase_name
            , scase_args = scase_args
            , scase_cmd = commandOpening (freeVarNamesToXtorArgs scase_args) (openCommandComplete scase_cmd)
            }
  in XMatch pc ns (openSCase <$> cases)
openSTermComplete (MuAbs PrdRep fv cmd) =
  MuAbs PrdRep fv (commandOpeningSingle CnsRep (FreeVar CnsRep fv) (openCommandComplete cmd))
openSTermComplete (MuAbs CnsRep fv cmd) =
  MuAbs CnsRep fv (commandOpeningSingle PrdRep (FreeVar PrdRep fv) (openCommandComplete cmd))

openCommandComplete :: Command FreeVarName -> Command FreeVarName
openCommandComplete (Apply t1 t2) = Apply (openSTermComplete t1) (openSTermComplete t2)
openCommandComplete (Print t) = Print (openSTermComplete t)
openCommandComplete Done = Done
