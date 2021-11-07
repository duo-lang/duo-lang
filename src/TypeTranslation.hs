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
import Syntax.Program
import Syntax.Types

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

newtype TranslateReader = TranslateReader { recVarMap :: Map TypeName TVar }

initialReader :: Environment -> (Environment, TranslateReader)
initialReader env = (env, TranslateReader { recVarMap = M.empty })

newtype TranslateM a = TraM { getTraM :: ReaderT (Environment, TranslateReader) (StateT TranslateState (Except Error)) a }
  deriving (Functor, Applicative, Monad, MonadState TranslateState, MonadReader (Environment, TranslateReader), MonadError Error)

runTranslateM :: Environment -> TranslateM a -> Either Error (a, TranslateState)
runTranslateM env m = runExcept (runStateT (runReaderT (getTraM m) (initialReader env)) initialState)

---------------------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------------------

withVarMap :: (Map TypeName TVar -> Map TypeName TVar) -> TranslateM a -> TranslateM a
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

-- | Translate all producer and consumer types in an xtor signature
translateXtorSigUpper' :: XtorSig Neg -> TranslateM (XtorSig Neg)
translateXtorSigUpper' MkXtorSig{..} = do
  -- Translate producer and consumer arg types recursively
  pts' <- mapM translateTypeUpper' $ prdTypes sig_args
  cts' <- mapM translateTypeLower' $ cnsTypes sig_args
  return $ MkXtorSig sig_name (MkTypArgs pts' cts')
    {- where
      xtorNameMakeStructural :: XtorName -> XtorName
      xtorNameMakeStructural (MkXtorName _ s) = MkXtorName Structural s -}

-- | Translate a nominal type into a structural type recursively
translateTypeUpper' :: Typ Neg -> TranslateM (Typ Neg)
translateTypeUpper' (TyNominal pr tn) = do
  m <- asks $ recVarMap . snd
  -- If current type name contained in cache, return corresponding rec. type variable
  if M.member tn m then do
    let tv = fromJust (M.lookup tn m)
    modifyVarsUsed $ S.insert tv -- add rec. type variable to used var cache
    return $ TyVar pr tv
  else do
    NominalDecl{..} <- lookupTypeName tn
    tv <- freshTVar
    case data_polarity of
      Data -> do
        -- Recursively translate xtor sig with mapping of current type name to new rec type var
        xtss <- mapM (withVarMap (M.insert tn tv) . translateXtorSigUpper') $ data_xtors pr
        return $ TyRec pr tv $ TyData pr (Just tn) xtss
      Codata -> do
        -- Recursively translate xtor sig with mapping of current type name to new rec type var
        xtss <- mapM (withVarMap (M.insert tn tv) . translateXtorSigLower') $ data_xtors $ flipPolarityRep pr
        return $ TyRec pr tv $ TyCodata pr (Just tn) xtss
translateTypeUpper' tv@TyVar{} = return tv
translateTypeUpper' ty = throwOtherError ["Cannot translate type " <> ppPrint ty]

---------------------------------------------------------------------------------------------
-- Lower bound translation functions
---------------------------------------------------------------------------------------------

-- | Translate all producer and consumer types in an xtor signature
translateXtorSigLower' :: XtorSig Pos -> TranslateM (XtorSig Pos)
translateXtorSigLower' MkXtorSig{..} = do
  -- Translate producer and consumer arg types recursively
  pts' <- mapM translateTypeLower' $ prdTypes sig_args
  cts' <- mapM translateTypeUpper' $ cnsTypes sig_args
  return $ MkXtorSig sig_name (MkTypArgs pts' cts')
    {- where
      xtorNameMakeStructural :: XtorName -> XtorName
      xtorNameMakeStructural (MkXtorName _ s) = MkXtorName Structural s -}

-- | Translate a nominal type into a structural type recursively
translateTypeLower' :: Typ Pos -> TranslateM (Typ Pos)
translateTypeLower' (TyNominal pr tn) = do
  m <- asks $ recVarMap . snd
  -- If current type name contained in cache, return corresponding rec. type variable
  if M.member tn m then do
    let tv = fromJust (M.lookup tn m)
    modifyVarsUsed $ S.insert tv -- add rec. type variable to used var cache
    return $ TyVar pr tv
  else do
    NominalDecl{..} <- lookupTypeName tn
    tv <- freshTVar
    case data_polarity of
      Data -> do
        -- Recursively translate xtor sig with mapping of current type name to new rec type var
        xtss <- mapM (withVarMap (M.insert tn tv) . translateXtorSigLower') $ data_xtors pr
        return $ TyRec pr tv $ TyData pr (Just tn) xtss
      Codata -> do
        -- Recursively translate xtor sig with mapping of current type name to new rec type var
        xtss <- mapM (withVarMap (M.insert tn tv) . translateXtorSigUpper') $ data_xtors $ flipPolarityRep pr
        return $ TyRec pr tv $ TyCodata pr (Just tn) xtss
translateTypeLower' tv@TyVar{} = return tv
translateTypeLower' ty = throwOtherError ["Cannot translate type " <> ppPrint ty]

---------------------------------------------------------------------------------------------
-- Cleanup functions
---------------------------------------------------------------------------------------------

cleanUpXtorSig :: XtorSig pol -> TranslateM (XtorSig pol)
cleanUpXtorSig MkXtorSig{..} = do
  pts <- mapM cleanUpType $ prdTypes sig_args
  cts <- mapM cleanUpType $ cnsTypes sig_args
  return MkXtorSig{ sig_name, sig_args = MkTypArgs pts cts }

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
