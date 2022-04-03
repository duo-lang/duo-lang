module TypeTranslation
  ( translateTypeUpper
  , translateXtorSigUpper
  , translateTypeLower
  , translateXtorSigLower
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Maybe
import Data.Map qualified as M
import Data.Set
import Data.Set qualified as S
import Data.Text qualified as T

import Errors
import Lookup
import Pretty.Pretty
import Pretty.Types ()
import Driver.Environment
import Syntax.RST.Types
import Syntax.Common

---------------------------------------------------------------------------------------------
-- TranslationState:
--
-- We store mappings of recursive type variables
---------------------------------------------------------------------------------------------

data TranslateState = TranslateState
  { recVarsUsed :: Set TVar
  , varCount :: Int }

initialState :: TranslateState
initialState = TranslateState { recVarsUsed = S.empty, varCount = 0 }

newtype TranslateReader = TranslateReader { recVarMap :: M.Map TypeName TVar }

initialReader :: Environment -> (Environment, TranslateReader)
initialReader env = (env, TranslateReader { recVarMap = M.empty })

newtype TranslateM a = TraM { getTraM :: ReaderT (Environment, TranslateReader) (StateT TranslateState (Except Error)) a }
  deriving (Functor, Applicative, Monad, MonadState TranslateState, MonadReader (Environment, TranslateReader), MonadError Error)

runTranslateM :: Environment -> TranslateM a -> Either Error (a, TranslateState)
runTranslateM env m = runExcept (runStateT (runReaderT (getTraM m) (initialReader env)) initialState)

---------------------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------------------

withVarMap :: (M.Map TypeName TVar -> M.Map TypeName TVar) -> TranslateM a -> TranslateM a
withVarMap f m = do
  local (\(env,TranslateReader{..}) ->
    (env,TranslateReader{ recVarMap = f recVarMap })) m

modifyVarsUsed :: (Set TVar -> Set TVar) -> TranslateM ()
modifyVarsUsed f = do
  modify (\TranslateState{..} ->
    TranslateState{ recVarsUsed = f recVarsUsed, varCount })

freshTVar :: TranslateM TVar
freshTVar = do
  i <- gets varCount
  modify (\TranslateState{..} ->
    TranslateState{ recVarsUsed, varCount = varCount + 1 })
  return $ MkTVar ("g" <> T.pack (show i))

---------------------------------------------------------------------------------------------
-- Upper bound translation functions
---------------------------------------------------------------------------------------------

translatePCTypeUpper :: PrdCnsType Neg -> TranslateM (PrdCnsType Neg)
translatePCTypeUpper (PrdCnsType PrdRep ty) = PrdCnsType PrdRep <$> translateTypeUpper' ty
translatePCTypeUpper (PrdCnsType CnsRep ty) = PrdCnsType CnsRep <$> translateTypeLower' ty

translateCtxtUpper :: LinearContext Neg -> TranslateM (LinearContext Neg)
translateCtxtUpper ctxt = sequence (translatePCTypeUpper <$> ctxt)

-- | Translate all producer and consumer types in an xtor signature
translateXtorSigUpper' :: XtorSig Neg -> TranslateM (XtorSig Neg)
translateXtorSigUpper' MkXtorSig{..} = do
  -- Translate producer and consumer arg types recursively
  ctxt <- translateCtxtUpper sig_args
  return $ MkXtorSig sig_name ctxt

-- | Translate a nominal type into a structural type recursively
translateTypeUpper' :: Typ Neg -> TranslateM (Typ Neg)
translateTypeUpper' (TyNominal NegRep _ tn _ _) = do
  m <- asks $ recVarMap . snd
  -- If current type name contained in cache, return corresponding rec. type variable
  if M.member tn m then do
    let tv = fromJust (M.lookup tn m)
    modifyVarsUsed $ S.insert tv -- add rec. type variable to used var cache
    return $ TyVar NegRep Nothing tv
  else do
    NominalDecl{..} <- lookupTypeName tn
    tv <- freshTVar
    case data_polarity of
      Data -> do
        -- Recursively translate xtor sig with mapping of current type name to new rec type var
        xtss <- mapM (withVarMap (M.insert tn tv) . translateXtorSigUpper') $ snd data_xtors
        return $ TyRec NegRep tv $ TyData NegRep (Just tn) xtss
      Codata -> do
        -- Upper bound translation of codata is empty
        return $ TyRec NegRep tv $ TyCodata NegRep (Just tn) []
translateTypeUpper' tv@TyVar{} = return tv
translateTypeUpper' ty = throwOtherError ["Cannot translate type " <> ppPrint ty]

---------------------------------------------------------------------------------------------
-- Lower bound translation functions
---------------------------------------------------------------------------------------------

translatePCTypeLower :: PrdCnsType Pos -> TranslateM (PrdCnsType Pos)
translatePCTypeLower (PrdCnsType PrdRep ty) = PrdCnsType PrdRep <$> translateTypeLower' ty
translatePCTypeLower (PrdCnsType CnsRep ty) = PrdCnsType CnsRep <$> translateTypeUpper' ty

translateCtxtLower :: LinearContext Pos -> TranslateM (LinearContext Pos)
translateCtxtLower ctxt = sequence (translatePCTypeLower <$> ctxt)

-- | Translate all producer and consumer types in an xtor signature
translateXtorSigLower' :: XtorSig Pos -> TranslateM (XtorSig Pos)
translateXtorSigLower' MkXtorSig{..} = do
  -- Translate producer and consumer arg types recursively
  ctxt <- translateCtxtLower sig_args
  return $ MkXtorSig sig_name ctxt

-- | Translate a nominal type into a structural type recursively
translateTypeLower' :: Typ Pos -> TranslateM (Typ Pos)
translateTypeLower' (TyNominal pr _ tn _ _) = do
  m <- asks $ recVarMap . snd
  -- If current type name contained in cache, return corresponding rec. type variable
  if M.member tn m then do
    let tv = fromJust (M.lookup tn m)
    modifyVarsUsed $ S.insert tv -- add rec. type variable to used var cache
    return $ TyVar pr Nothing tv
  else do
    NominalDecl{..} <- lookupTypeName tn
    tv <- freshTVar
    case data_polarity of
      Data -> do
        -- Lower bound translation of data is empty
        return $ TyRec pr tv $ TyData pr (Just tn) []
      Codata -> do
        -- Recursively translate xtor sig with mapping of current type name to new rec type var
        xtss <- mapM (withVarMap (M.insert tn tv) . translateXtorSigUpper') $ snd data_xtors
        return $ TyRec pr tv $ TyCodata pr (Just tn) xtss
translateTypeLower' tv@TyVar{} = return tv
translateTypeLower' ty = throwOtherError ["Cannot translate type " <> ppPrint ty]

---------------------------------------------------------------------------------------------
-- Cleanup functions
---------------------------------------------------------------------------------------------

cleanUpPCType :: PrdCnsType pol -> TranslateM (PrdCnsType pol)
cleanUpPCType (PrdCnsType rep ty) = PrdCnsType rep <$> cleanUpType ty

cleanUpCtxt :: LinearContext pol -> TranslateM (LinearContext pol)
cleanUpCtxt ctxt = sequence (cleanUpPCType <$> ctxt)

cleanUpXtorSig :: XtorSig pol -> TranslateM (XtorSig pol)
cleanUpXtorSig MkXtorSig{..} = do
  ctxt <- cleanUpCtxt sig_args
  return MkXtorSig{ sig_name, sig_args = ctxt }

-- | Remove unused recursion headers
cleanUpType :: Typ pol -> TranslateM (Typ pol)
cleanUpType ty = case ty of
  -- Remove outermost recursive type if its variable is unused
  TyRec pr tv ty' -> do
    s <- gets recVarsUsed
    tyClean <- cleanUpType ty' -- propagate cleanup
    if S.member tv s then return $ TyRec pr tv tyClean
    else return tyClean
  -- Propagate cleanup for data and codata types
  TyData pr mtn xtss -> do
    xtss' <- mapM cleanUpXtorSig xtss
    return $ TyData pr mtn xtss'
  TyCodata pr mtn xtss -> do
    xtss' <- mapM cleanUpXtorSig xtss
    return $ TyCodata pr mtn xtss'
  -- Type variables remain unchanged
  tv@TyVar{} -> return tv
  -- Other types imply incorrect translation
  t -> throwOtherError ["Type translation: Cannot clean up type " <> ppPrint t]

---------------------------------------------------------------------------------------------
-- Exported functions
---------------------------------------------------------------------------------------------

translateTypeUpper :: Environment -> Typ Neg -> Either Error (Typ Neg)
translateTypeUpper env ty = case runTranslateM env $ cleanUpType =<< translateTypeUpper' ty of
  Left err -> throwError err
  Right (ty',_) -> return ty'

translateXtorSigUpper :: Environment -> XtorSig Neg -> Either Error (XtorSig Neg)
translateXtorSigUpper env xts = case runTranslateM env $ cleanUpXtorSig =<< translateXtorSigUpper' xts of
  Left err -> throwError err
  Right (xts',_) -> return xts'

translateTypeLower :: Environment -> Typ Pos -> Either Error (Typ Pos)
translateTypeLower env ty = case runTranslateM env $ cleanUpType =<< translateTypeLower' ty of
  Left err -> throwError err
  Right (ty',_) -> return ty'

translateXtorSigLower :: Environment -> XtorSig Pos -> Either Error (XtorSig Pos)
translateXtorSigLower env xts = case runTranslateM env $ cleanUpXtorSig =<< translateXtorSigLower' xts of
  Left err -> throwError err
  Right (xts',_) -> return xts'
