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
  { recVarMap :: Map TypeName TVar
  , recVarsUsed :: Set TVar
  , varCount :: Int }

initialState :: TranslateState
initialState = TranslateState { recVarMap = M.empty, recVarsUsed = S.empty, varCount = 0 }

newtype TranslateReader = TranslateReader { context :: [TypArgs Pos] }

initialReader :: Environment FreeVarName -> (Environment FreeVarName, TranslateReader)
initialReader env = (env, TranslateReader { context = [] })

newtype TranslateM a = TraM { getTraM :: ReaderT (Environment FreeVarName, TranslateReader) (StateT TranslateState (Except Error)) a }
  deriving (Functor, Applicative, Monad, MonadState TranslateState, MonadReader (Environment FreeVarName, TranslateReader), MonadError Error)

runTranslateM :: Environment FreeVarName -> TranslateM a -> Either Error (a, TranslateState)
runTranslateM env m = runExcept (runStateT (runReaderT (getTraM m) (initialReader env)) initialState)

---------------------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------------------

modifyVarMap :: (Map TypeName TVar -> Map TypeName TVar) -> TranslateM ()
modifyVarMap f = do
  modify (\TranslateState{..} -> 
    TranslateState{ recVarMap = f recVarMap, recVarsUsed, varCount })

modifyVarSet :: (Set TVar -> Set TVar) -> TranslateM ()
modifyVarSet f = do
  modify (\TranslateState{..} ->
    TranslateState{ recVarMap, recVarsUsed = f recVarsUsed, varCount })

freshTVar :: TranslateM TVar
freshTVar = do
  i <- gets varCount
  modify (\TranslateState{..} ->
    TranslateState{ recVarMap, recVarsUsed, varCount = varCount + 1 })
  return $ MkTVar ("g" <> T.pack (show i))

---------------------------------------------------------------------------------------------
-- Translation functions
---------------------------------------------------------------------------------------------

-- | Translate all producer and consumer types in an xtor signature
translateXtorSig' :: XtorSig pol -> TranslateM (XtorSig pol)
translateXtorSig' MkXtorSig{..} = do
  pts' <- mapM translateType' $ prdTypes sig_args
  cts' <- mapM translateType' $ cnsTypes sig_args
  return $ MkXtorSig (xtorNameMakeStructural sig_name) (MkTypArgs pts' cts')
    where
      xtorNameMakeStructural :: XtorName -> XtorName
      xtorNameMakeStructural (MkXtorName _ s) = MkXtorName Structural s

-- | Translate a nominal type into a structural type recursively
translateType' :: Typ pol -> TranslateM (Typ pol)
translateType' (TyNominal pr tn) = do
  m <- gets recVarMap
  -- If current type name contained in cache, return corresponding rec. type variable
  if M.member tn m then do
    let tv = fromJust (M.lookup tn m)
    modifyVarSet $ S.insert tv -- add rec. type variable to used var cache
    return $ TyVar pr tv
  else do
    NominalDecl{..} <- lookupTypeName tn
    tv <- freshTVar
    -- Insert current type name into cache with corresponding rec. type variable
    modifyVarMap $ M.insert tn tv
    case data_polarity of
      Data -> do
        xtss <- mapM translateXtorSig' $ data_xtors pr
        return $ TyRec pr tv $ TyData pr xtss
      Codata -> do
        xtss <- mapM translateXtorSig' $ data_xtors $ flipPolarityRep pr
        return $ TyRec pr tv $ TyCodata pr xtss
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
  Left (OtherError err) -> throwOtherError [err]
  Left _ -> throwOtherError []
  Right (ty,_) -> return ty

translateXtorSig :: Environment FreeVarName -> XtorSig pol -> Either Error (XtorSig pol)
translateXtorSig env xts = case runTranslateM env $ (cleanUpXtorSig <=< translateXtorSig') xts of
  Left (OtherError err) -> throwOtherError [err]
  Left _ -> throwOtherError []
  Right (xts,_) -> return xts