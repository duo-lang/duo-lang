module TypeTranslation
  ( translateType
  , translateXtorSig
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set
import qualified Data.Set as S
import qualified Data.Text as T

import Errors
import Lookup
import Pretty.Pretty
import Pretty.Types ()
import Syntax.Program
import Syntax.Types
import Syntax.CommonTerm

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

initialReader :: Environment FreeVarName -> (Environment FreeVarName, TranslateReader)
initialReader env = (env, TranslateReader { recVarMap = M.empty })

newtype TranslateM a = TraM { getTraM :: ReaderT (Environment FreeVarName, TranslateReader) (StateT TranslateState (Except Error)) a }
  deriving (Functor, Applicative, Monad, MonadState TranslateState, MonadReader (Environment FreeVarName, TranslateReader), MonadError Error)

runTranslateM :: Environment FreeVarName -> TranslateM a -> Either Error (a, TranslateState)
runTranslateM env m = runExcept (runStateT (runReaderT (getTraM m) (initialReader env)) initialState)

---------------------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------------------

withVarMap :: (Map TypeName TVar -> Map TypeName TVar) -> TranslateM a -> TranslateM a
withVarMap f m = do
  local (\(env,TranslateReader{..}) -> 
    (env,TranslateReader{ recVarMap = f recVarMap })) m

modifyVarSet :: (Set TVar -> Set TVar) -> TranslateM ()
modifyVarSet f = do
  modify (\TranslateState{..} ->
    TranslateState{ recVarsUsed = f recVarsUsed, varCount })

freshTVar :: TranslateM TVar
freshTVar = do
  i <- gets varCount
  modify (\TranslateState{..} ->
    TranslateState{ recVarsUsed, varCount = varCount + 1 })
  return $ MkTVar ("g" <> T.pack (show i))

---------------------------------------------------------------------------------------------
-- Translation functions
---------------------------------------------------------------------------------------------

-- | Translate all producer and consumer types in an xtor signature
translateXtorSig' :: XtorSig pol -> TranslateM (XtorSig pol)
translateXtorSig' MkXtorSig{..} = do
  pts' <- mapM translateType' $ prdTypes sig_args
  cts' <- mapM translateType' $ cnsTypes sig_args
  return $ MkXtorSig sig_name (MkTypArgs pts' cts')
    {- where
      xtorNameMakeStructural :: XtorName -> XtorName
      xtorNameMakeStructural (MkXtorName _ s) = MkXtorName Structural s -}

-- | Translate a nominal type into a structural type recursively
translateType' :: Typ pol -> TranslateM (Typ pol)
translateType' (TyNominal pr tn) = do
  m <- asks $ recVarMap . snd
  -- If current type name contained in cache, return corresponding rec. type variable
  if M.member tn m then do
    let tv = fromJust (M.lookup tn m)
    modifyVarSet $ S.insert tv -- add rec. type variable to used var cache
    return $ TyVar pr tv
  else do
    NominalDecl{..} <- lookupTypeName tn
    tv <- freshTVar
    case data_polarity of
      Data -> do
        -- Recursively translate xtor sig with mapping of current type name to new rec type var
        xtss <- mapM (withVarMap (M.insert tn tv) . translateXtorSig') $ data_xtors pr
        return $ TyRec pr tv $ TyData pr xtss
      Codata -> do
        -- Recursively translate xtor sig with mapping of current type name to new rec type var
        xtss <- mapM (withVarMap (M.insert tn tv) . translateXtorSig') $ data_xtors $ flipPolarityRep pr
        return $ TyRec pr tv $ TyCodata pr xtss
translateType' tv@TyVar{} = return tv
translateType' t = throwOtherError ["Cannot translate type " <> ppPrint t]

---------------------------------------------------------------------------------------------
-- Cleanup functions
---------------------------------------------------------------------------------------------

cleanUpXtorSig :: XtorSig pol -> TranslateM (XtorSig pol)
cleanUpXtorSig MkXtorSig{..} = do
  pts <- mapM cleanUp $ prdTypes sig_args
  cts <- mapM cleanUp $ cnsTypes sig_args
  return MkXtorSig{ sig_name, sig_args = MkTypArgs pts cts }

-- | Remove unused recursion headers
cleanUp :: Typ pol -> TranslateM (Typ pol)
cleanUp ty = case ty of
  -- Remove outermost recursive type if its variable is unused
  TyRec pr tv ty' -> do
    s <- gets recVarsUsed
    ty'Clean <- cleanUp ty'
    if S.member tv s then return $ TyRec pr tv ty'Clean
    else return ty'Clean
  -- Propagate cleanup in arg types of data type
  TyData pr xtss -> do
    xtss' <- mapM cleanUpXtorSig xtss
    return $ TyData pr xtss'
  -- Propagate cleanup in arg types of codata type
  TyCodata pr xtss -> do
    xtss' <- mapM cleanUpXtorSig xtss
    return $ TyCodata pr xtss'
  -- Type variables remain unchanged
  tyVar@TyVar{} -> return tyVar
  -- Other types imply incorrect translation
  t -> throwOtherError ["Type translation: Cannot clean up type " <> ppPrint t]

translateType :: Environment FreeVarName -> Typ pol -> Either Error (Typ pol)
translateType env ty = case runTranslateM env $ (cleanUp <=< translateType') ty of
  Left err -> throwError err
  Right (ty,_) -> return ty
  

translateXtorSig :: Environment FreeVarName -> XtorSig pol -> Either Error (XtorSig pol)
translateXtorSig env xts = case runTranslateM env $ (cleanUpXtorSig <=< translateXtorSig') xts of
  Left err -> throwError err
  Right (xts,_) -> return xts