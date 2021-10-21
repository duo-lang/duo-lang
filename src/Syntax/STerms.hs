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
  -- Transform to named representation for prettyprinting
  , openSTermComplete
  , openCommandComplete
  , createNamesSTerm
  , createNamesCommand
  -- Shift unbound BoundVars up by one.
  , shiftSTerm
  , shiftCmd
  ) where

import Control.Monad.State
import Data.Bifunctor
import Data.List (elemIndex)
import Data.Maybe (fromJust, isJust)
import qualified Data.Text as T

import Utils
import Errors
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
data XtorArgs ext bs = MkXtorArgs { prdArgs :: [STerm Prd ext bs]
                                  , cnsArgs :: [STerm Cns ext bs]
                                  }
  deriving (Show, Eq, Functor)

instance Bifunctor XtorArgs where
  bimap f g MkXtorArgs { prdArgs, cnsArgs } =
    MkXtorArgs (bimap f g <$> prdArgs) (bimap f g <$> cnsArgs)

-- | Represents one case in a pattern match or copattern match.
--
--        X(x_1,...,x_n)[k_1,...,k_m] => c
--        ^ ^^^^^^^^^^^^^^^^^^^^^^^^     ^
--        |              |               |
--    scase_name     scase_args      scase_cmd
--
data SCase ext bs = MkSCase
  { scase_name :: XtorName
  , scase_args :: Twice [bs]
  , scase_cmd  :: Command ext bs
  } deriving (Show, Eq, Functor)

instance Bifunctor SCase where
  bimap f g MkSCase { scase_name, scase_args, scase_cmd } =
    MkSCase scase_name (fmap g <$> scase_args)  (bimap f g scase_cmd)

-- | A symmetric term.
-- The `bs` parameter is used to store additional information at binding sites.
data STerm (pc :: PrdCns) ext bs where
  -- | A bound variable in the locally nameless system.
  BoundVar :: ext -> PrdCnsRep pc -> Index -> STerm pc ext bs
  -- | A free variable in the locally nameless system.
  FreeVar :: ext -> PrdCnsRep pc -> FreeVarName -> STerm pc ext bs
  -- | A constructor or destructor.
  -- If the first argument is `PrdRep` it is a constructor, a destructor otherwise.
  XtorCall :: ext -> PrdCnsRep pc -> XtorName -> XtorArgs ext bs -> STerm pc ext bs
  -- | A pattern or copattern match.
  -- If the first argument is `PrdRep` it is a copattern match, a pattern match otherwise.
  XMatch :: ext -> PrdCnsRep pc -> NominalStructural -> [SCase ext bs] -> STerm pc ext bs
  -- | A Mu or TildeMu abstraction:
  --
  --  mu k.c    =   MuAbs PrdRep c
  -- ~mu x.c    =   MuAbs CnsRep c
  MuAbs :: ext -> PrdCnsRep pc -> bs -> Command ext bs -> STerm pc ext bs
  deriving (Eq)
deriving instance (Show bs, Show ext) => Show (STerm pc ext bs)
deriving instance Functor (STerm pc ext)

instance Bifunctor (STerm pc) where
  bimap f _ (BoundVar ext rep idx) = BoundVar (f ext) rep idx
  bimap f _ (FreeVar ext rep v) = FreeVar (f ext) rep v
  bimap f g (XtorCall ext pc xt args) = XtorCall (f ext) pc xt (bimap f g args)
  bimap f g (XMatch ext pc ns cases) = XMatch (f ext) pc ns (bimap f g <$> cases)
  bimap f g (MuAbs ext pc bs cmd) = MuAbs (f ext) pc (g bs) (bimap f g cmd)

---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------

-- | An executable command.
data Command ext bs
  -- | A producer applied to a consumer:
  --
  --   p >> c
  = Apply ext (STerm Prd ext bs) (STerm Cns ext bs)
  | Print ext (STerm Prd ext bs)
  | Done ext
  deriving (Show, Eq, Functor)

instance Bifunctor Command where
  bimap f g (Apply ext prd cns) = Apply (f ext) (bimap f g prd) (bimap f g cns)
  bimap f g (Print ext prd) = Print (f ext) (bimap f g prd)
  bimap f _ (Done ext) = Done (f ext)

---------------------------------------------------------------------------------
-- Variable Opening
---------------------------------------------------------------------------------

termOpeningRec :: Int -> XtorArgs () bs -> STerm pc () bs -> STerm pc () bs
termOpeningRec k MkXtorArgs { prdArgs } bv@(BoundVar _ PrdRep (i,j)) | i == k    = prdArgs !! j
                                                                     | otherwise = bv
termOpeningRec k MkXtorArgs { cnsArgs } bv@(BoundVar _ CnsRep (i,j)) | i == k    = cnsArgs !! j
                                                                     | otherwise = bv
termOpeningRec _ _ fv@(FreeVar _ _ _)       = fv
termOpeningRec k args (XtorCall _ s xt (MkXtorArgs prdArgs cnsArgs)) =
  XtorCall () s xt (MkXtorArgs (termOpeningRec k args <$> prdArgs)
                               (termOpeningRec k args <$> cnsArgs))
termOpeningRec k args (XMatch _ pc sn cases) =
  XMatch () pc sn $ map (\pmcase@MkSCase{ scase_cmd } -> pmcase { scase_cmd = commandOpeningRec (k+1) args scase_cmd }) cases
termOpeningRec k args (MuAbs _ pc a cmd) =
  MuAbs () pc a (commandOpeningRec (k+1) args cmd)

commandOpeningRec :: Int -> XtorArgs () bs -> Command () bs -> Command () bs
commandOpeningRec _ _ (Done _) = Done ()
commandOpeningRec k args (Print _ t) = Print () (termOpeningRec k args t)
commandOpeningRec k args (Apply _ t1 t2) = Apply () (termOpeningRec k args t1) (termOpeningRec k args t2)


-- replaces bound variables pointing "outside" of a command with given arguments
commandOpening :: XtorArgs () a -> Command () a -> Command () a
commandOpening = commandOpeningRec 0

commandOpeningSingle :: PrdCnsRep pc -> STerm pc () a -> Command () a -> Command () a
commandOpeningSingle PrdRep t = commandOpening (MkXtorArgs [t] [])
commandOpeningSingle CnsRep t = commandOpening (MkXtorArgs [] [t])

---------------------------------------------------------------------------------
-- Variable Closing
---------------------------------------------------------------------------------

termClosingRec :: Int -> Twice [FreeVarName] -> STerm pc ext bs -> STerm pc ext bs
termClosingRec _ _ bv@(BoundVar _ _ _) = bv
termClosingRec k (Twice prdvars _) (FreeVar ext PrdRep v) | isJust (v `elemIndex` prdvars) = BoundVar ext PrdRep (k, fromJust (v `elemIndex` prdvars))
                                                          | otherwise = FreeVar ext PrdRep v
termClosingRec k (Twice _ cnsvars) (FreeVar ext CnsRep v) | isJust (v `elemIndex` cnsvars) = BoundVar ext CnsRep (k, fromJust (v `elemIndex` cnsvars))
                                                          | otherwise = FreeVar ext CnsRep v
termClosingRec k vars (XtorCall ext s xt (MkXtorArgs prdArgs cnsArgs)) =
  XtorCall ext s xt (MkXtorArgs (termClosingRec k vars <$> prdArgs)(termClosingRec k vars <$> cnsArgs))
termClosingRec k vars (XMatch ext pc sn cases) =
  XMatch ext pc sn $ map (\pmcase@MkSCase { scase_cmd } -> pmcase { scase_cmd = commandClosingRec (k+1) vars scase_cmd }) cases
termClosingRec k vars (MuAbs ext pc a cmd) =
  MuAbs ext pc a (commandClosingRec (k+1) vars cmd)

commandClosingRec :: Int -> Twice [FreeVarName] -> Command ext bs -> Command ext bs
commandClosingRec _ _ (Done ext) = Done ext
commandClosingRec k args (Print ext t) = Print ext (termClosingRec k args t)
commandClosingRec k args (Apply ext t1 t2) = Apply ext (termClosingRec k args t1) (termClosingRec k args t2)

commandClosing :: Twice [FreeVarName] -> Command ext bs -> Command ext bs
commandClosing = commandClosingRec 0

commandClosingSingle :: PrdCnsRep pc -> FreeVarName -> Command ext bs -> Command ext bs
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

termLocallyClosedRec :: [Twice [()]] -> STerm pc () a -> Either Error ()
termLocallyClosedRec env (BoundVar _ pc idx) = checkIfBound env pc idx
termLocallyClosedRec _ (FreeVar _ _ _) = Right ()
termLocallyClosedRec env (XtorCall _ _ _ (MkXtorArgs prds cnss)) = do
  sequence_ (termLocallyClosedRec env <$> prds)
  sequence_ (termLocallyClosedRec env <$> cnss)
termLocallyClosedRec env (XMatch _ _ _ cases) = do
  sequence_ ((\MkSCase { scase_cmd, scase_args } -> commandLocallyClosedRec (twiceMap (fmap (const ())) (fmap (const ())) scase_args : env) scase_cmd) <$> cases)
termLocallyClosedRec env (MuAbs _ PrdRep _ cmd) = commandLocallyClosedRec (Twice [] [()] : env) cmd
termLocallyClosedRec env (MuAbs _ CnsRep _ cmd) = commandLocallyClosedRec (Twice [()] [] : env) cmd

commandLocallyClosedRec :: [Twice [()]] -> Command () a -> Either Error ()
commandLocallyClosedRec _ (Done _) = Right ()
commandLocallyClosedRec env (Print _ t) = termLocallyClosedRec env t
commandLocallyClosedRec env (Apply _ t1 t2) = termLocallyClosedRec env t1 >> termLocallyClosedRec env t2

termLocallyClosed :: STerm pc () a -> Either Error ()
termLocallyClosed = termLocallyClosedRec []

commandLocallyClosed :: Command () a -> Either Error ()
commandLocallyClosed = commandLocallyClosedRec []

---------------------------------------------------------------------------------
-- These functions  translate a locally nameless term into a named representation.
--
-- Use only for prettyprinting! These functions only "undo" the steps in the parser
-- and do not fulfil any semantic properties w.r.t shadowing etc.!
---------------------------------------------------------------------------------

openXtorArgsComplete :: XtorArgs ext FreeVarName -> XtorArgs () FreeVarName
openXtorArgsComplete (MkXtorArgs prdArgs cnsArgs) =
  MkXtorArgs (openSTermComplete <$> prdArgs) (openSTermComplete <$> cnsArgs)

freeVarNamesToXtorArgs :: Twice [FreeVarName] -> XtorArgs () FreeVarName
freeVarNamesToXtorArgs (Twice prds cnss) = MkXtorArgs ((\n -> FreeVar () PrdRep n) <$> prds) ((\n -> FreeVar () CnsRep n) <$> cnss)

openSTermComplete :: STerm pc ext FreeVarName -> STerm pc () FreeVarName
openSTermComplete (BoundVar _ pc idx) = BoundVar () pc idx
openSTermComplete (FreeVar _ pc v) = FreeVar () pc v
openSTermComplete (XtorCall _ pc name args) = XtorCall () pc name (openXtorArgsComplete args)
openSTermComplete (XMatch _ pc ns cases) = let
  openSCase :: SCase ext FreeVarName -> SCase () FreeVarName
  openSCase MkSCase { scase_name, scase_args, scase_cmd } =
    MkSCase { scase_name = scase_name
            , scase_args = scase_args
            , scase_cmd = commandOpening (freeVarNamesToXtorArgs scase_args) (openCommandComplete scase_cmd)
            }
  in XMatch () pc ns (openSCase <$> cases)
openSTermComplete (MuAbs _ PrdRep fv cmd) =
  MuAbs () PrdRep fv (commandOpeningSingle CnsRep (FreeVar () CnsRep fv) (openCommandComplete cmd))
openSTermComplete (MuAbs _ CnsRep fv cmd) =
  MuAbs () CnsRep fv (commandOpeningSingle PrdRep (FreeVar () PrdRep fv) (openCommandComplete cmd))

openCommandComplete :: Command ext FreeVarName -> Command () FreeVarName
openCommandComplete (Apply _ t1 t2) = Apply () (openSTermComplete t1) (openSTermComplete t2)
openCommandComplete (Print _ t) = Print () (openSTermComplete t)
openCommandComplete (Done _) = Done ()

---------------------------------------------------------------------------------
-- CreateNames
---------------------------------------------------------------------------------

names :: ([FreeVarName], [FreeVarName])
names =  ((\y -> "x" <> T.pack (show y)) <$> [(1 :: Int)..]
         ,(\y -> "k" <> T.pack (show y)) <$> [(1 :: Int)..])

type CreateNameM a = State ([FreeVarName],[FreeVarName]) a

fresh :: PrdCnsRep pc -> CreateNameM FreeVarName 
fresh PrdRep = do
  var <- gets (head . fst)
  modify (first tail)
  pure var
fresh CnsRep = do
  var  <- gets (head . snd)
  modify (second tail)
  pure var

createNamesSTerm :: STerm pc ext bs -> STerm pc ext FreeVarName 
createNamesSTerm tm = evalState (createNamesSTerm' tm) names

createNamesCommand :: Command ext bs -> Command ext FreeVarName 
createNamesCommand cmd = evalState (createNamesCommand' cmd) names

createNamesSTerm' :: STerm pc ext bs -> CreateNameM (STerm pc ext FreeVarName)
createNamesSTerm' (BoundVar ext pc idx) = return $ BoundVar ext pc idx
createNamesSTerm' (FreeVar ext pc nm)   = return $ FreeVar ext pc nm
createNamesSTerm' (XtorCall ext pc xt MkXtorArgs { prdArgs, cnsArgs}) = do
  prdArgs' <- sequence $ createNamesSTerm' <$> prdArgs
  cnsArgs' <- sequence $ createNamesSTerm' <$> cnsArgs
  return $ XtorCall ext pc xt (MkXtorArgs prdArgs' cnsArgs')
createNamesSTerm' (XMatch ext pc ns cases) = do
  cases' <- sequence $ createNamesCase <$> cases
  return $ XMatch ext pc ns cases'
createNamesSTerm' (MuAbs ext pc _ cmd) = do
  cmd' <- createNamesCommand' cmd
  var <- fresh (flipPrdCns pc)
  return $ MuAbs ext pc var cmd'

createNamesCommand' :: Command ext bs -> CreateNameM (Command ext FreeVarName)
createNamesCommand' (Done ext) = return $ Done ext
createNamesCommand' (Apply ext prd cns) = do
  prd' <- createNamesSTerm' prd 
  cns' <- createNamesSTerm' cns 
  return (Apply ext prd' cns')
createNamesCommand' (Print ext prd) = createNamesSTerm' prd >>= \prd' -> return (Print ext prd')

createNamesCase :: SCase ext bs -> CreateNameM (SCase ext FreeVarName)
createNamesCase (MkSCase {scase_name, scase_args = Twice as bs, scase_cmd }) = do
  cmd' <- createNamesCommand' scase_cmd
  as' <- sequence $ (const (fresh PrdRep)) <$> as
  bs' <- sequence $ (const (fresh CnsRep)) <$> bs
  return $ MkSCase scase_name (Twice as' bs') cmd'


---------------------------------------------------------------------------------
-- Shifting
--
-- Used in program transformations like focusing.
---------------------------------------------------------------------------------

shiftSTerm' :: Int -> STerm pc ext bs -> STerm pc ext bs
shiftSTerm' _ var@FreeVar {} = var
shiftSTerm' n (BoundVar ext pcrep (i,j)) | n <= i    = BoundVar ext pcrep (i + 1, j)
                                         | otherwise = BoundVar ext pcrep (i    , j)
shiftSTerm' n (XtorCall ext pcrep name MkXtorArgs { prdArgs, cnsArgs }) =
    XtorCall ext pcrep name (MkXtorArgs (shiftSTerm' n <$> prdArgs) (shiftSTerm' n <$> cnsArgs))
shiftSTerm' n (XMatch ext pcrep ns cases) = XMatch ext pcrep ns (shiftSCase (n + 1) <$> cases)
shiftSTerm' n (MuAbs ext pcrep bs cmd) = MuAbs ext pcrep bs (shiftCmd' (n + 1) cmd)

shiftSCase :: Int -> SCase ext bs -> SCase ext bs
shiftSCase n (MkSCase name bs cmd) = MkSCase name bs (shiftCmd' n cmd)

shiftCmd' :: Int -> Command ext bs -> Command ext bs
shiftCmd' n (Apply ext prd cns) = Apply ext (shiftSTerm' n prd) (shiftSTerm' n cns)
shiftCmd' _ (Done ext) = Done ext
shiftCmd' n (Print ext prd) = Print ext (shiftSTerm' n prd)

-- | Shift all unbound BoundVars up by one.
shiftSTerm :: STerm pc ext bs -> STerm pc ext bs
shiftSTerm = shiftSTerm' 0

-- | Shift all unbound BoundVars up by one.
shiftCmd :: Command ext bs -> Command ext bs 
shiftCmd = shiftCmd' 0
