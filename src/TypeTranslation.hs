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
import Data.Map (Map)
import Data.Map qualified as M
import Data.Set
import Data.Set qualified as S
import Data.Text qualified as T

import Errors
import Lookup
import Pretty.Pretty
import Pretty.Types ()
import Driver.Environment
import Syntax.Common.TypesPol
import Syntax.Common
import Utils

---------------------------------------------------------------------------------------------
-- TranslationState:
--
-- We store mappings of recursive type variables
---------------------------------------------------------------------------------------------

data TranslateState = TranslateState
  { recVarsUsed :: Set TSkolemVar
  , varCount :: Int }

initialState :: TranslateState
initialState = TranslateState { recVarsUsed = S.empty, varCount = 0 }

newtype TranslateReader = TranslateReader { recVarMap :: M.Map RnTypeName TSkolemVar }

initialReader :: Map ModuleName Environment -> (Map ModuleName Environment, TranslateReader)
initialReader env = (env, TranslateReader { recVarMap = M.empty })

newtype TranslateM a = TraM { getTraM :: ReaderT (Map ModuleName Environment, TranslateReader) (StateT TranslateState (Except Error)) a }
  deriving (Functor, Applicative, Monad, MonadState TranslateState, MonadReader (Map ModuleName Environment, TranslateReader), MonadError Error)

runTranslateM :: Map ModuleName Environment -> TranslateM a -> Either Error (a, TranslateState)
runTranslateM env m = runExcept (runStateT (runReaderT (getTraM m) (initialReader env)) initialState)

---------------------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------------------

withVarMap :: (M.Map RnTypeName TSkolemVar -> M.Map RnTypeName TSkolemVar) -> TranslateM a -> TranslateM a
withVarMap f m = do
  local (\(env,TranslateReader{..}) ->
    (env,TranslateReader{ recVarMap = f recVarMap })) m

modifyVarsUsed :: (Set TSkolemVar -> Set TSkolemVar) -> TranslateM ()
modifyVarsUsed f = do
  modify (\TranslateState{..} ->
    TranslateState{ recVarsUsed = f recVarsUsed, varCount })

freshSkolemTVar :: TranslateM TSkolemVar
freshSkolemTVar = do
  i <- gets varCount
  modify (\TranslateState{..} ->
    TranslateState{ recVarsUsed, varCount = varCount + 1 })
  return $ MkTSkolemVar ("g" <> T.pack (show i))

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
translateTypeUpper' (TyNominal _ NegRep _ tn _) = do
  m <- asks $ recVarMap . snd
  -- If current type name contained in cache, return corresponding rec. type variable
  if M.member tn m then do
    let tv = fromJust (M.lookup tn m)
    modifyVarsUsed $ S.insert tv -- add rec. type variable to used var cache
    return $ TySkolemVar defaultLoc NegRep Nothing tv
  else do
    NominalDecl{..} <- lookupTypeName tn
    tv <- freshSkolemTVar
    case data_polarity of
      Data -> do
        -- Recursively translate xtor sig with mapping of current type name to new rec type var
        xtss <- mapM (withVarMap (M.insert tn tv) . translateXtorSigUpper') $ snd data_xtors
        return $ TyRec defaultLoc NegRep tv $ TyData defaultLoc NegRep (Just tn) xtss
      Codata -> do
        -- Upper bound translation of codata is empty
        return $ TyRec defaultLoc NegRep tv $ TyCodata defaultLoc NegRep (Just tn) []
translateTypeUpper' tv@TySkolemVar{} = return tv
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
translateTypeLower' (TyNominal _ pr _ tn _) = do
  m <- asks $ recVarMap . snd
  -- If current type name contained in cache, return corresponding rec. type variable
  if M.member tn m then do
    let tv = fromJust (M.lookup tn m)
    modifyVarsUsed $ S.insert tv -- add rec. type variable to used var cache
    return $ TySkolemVar defaultLoc pr Nothing tv
  else do
    NominalDecl{..} <- lookupTypeName tn
    tv <- freshSkolemTVar
    case data_polarity of
      Data -> do
        -- Lower bound translation of data is empty
        return $ TyRec defaultLoc pr tv $ TyData defaultLoc pr (Just tn) []
      Codata -> do
        -- Recursively translate xtor sig with mapping of current type name to new rec type var
        xtss <- mapM (withVarMap (M.insert tn tv) . translateXtorSigUpper') $ snd data_xtors
        return $ TyRec defaultLoc pr tv $ TyCodata defaultLoc pr (Just tn) xtss
translateTypeLower' tv@TySkolemVar{} = return tv
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
  TyRec loc pr tv ty' -> do
    s <- gets recVarsUsed
    tyClean <- cleanUpType ty' -- propagate cleanup
    if S.member tv s then return $ TyRec loc pr tv tyClean
    else return tyClean
  -- Propagate cleanup for data and codata types
  TyData loc pr mtn xtss -> do
    xtss' <- mapM cleanUpXtorSig xtss
    return $ TyData loc pr mtn xtss'
  TyCodata loc pr mtn xtss -> do
    xtss' <- mapM cleanUpXtorSig xtss
    return $ TyCodata loc pr mtn xtss'
  -- Type variables remain unchanged
  tv@TySkolemVar{} -> return tv
  -- Other types imply incorrect translation
  t -> throwOtherError ["Type translation: Cannot clean up type " <> ppPrint t]

---------------------------------------------------------------------------------------------
-- Exported functions
---------------------------------------------------------------------------------------------

translateTypeUpper :: Map ModuleName Environment -> Typ Neg -> Either Error (Typ Neg)
translateTypeUpper env ty = case runTranslateM env $ cleanUpType =<< translateTypeUpper' ty of
  Left err -> throwError err
  Right (ty',_) -> return ty'

translateXtorSigUpper :: Map ModuleName Environment -> XtorSig Neg -> Either Error (XtorSig Neg)
translateXtorSigUpper env xts = case runTranslateM env $ cleanUpXtorSig =<< translateXtorSigUpper' xts of
  Left err -> throwError err
  Right (xts',_) -> return xts'

translateTypeLower :: Map ModuleName Environment -> Typ Pos -> Either Error (Typ Pos)
translateTypeLower env ty = case runTranslateM env $ cleanUpType =<< translateTypeLower' ty of
  Left err -> throwError err
  Right (ty',_) -> return ty'

translateXtorSigLower :: Map ModuleName Environment -> XtorSig Pos -> Either Error (XtorSig Pos)
translateXtorSigLower env xts = case runTranslateM env $ cleanUpXtorSig =<< translateXtorSigLower' xts of
  Left err -> throwError err
  Right (xts',_) -> return xts'
