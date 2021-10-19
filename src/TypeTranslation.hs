module TypeTranslation where

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

-- | Translate all producer and consumer types in an xtor signature
translateSigArgs :: XtorSig pol -> TranslateM (XtorSig pol)
translateSigArgs MkXtorSig{..} = do
  pts' <- mapM translateType $ prdTypes sig_args
  cts' <- mapM translateType $ cnsTypes sig_args
  return $ MkXtorSig (xtorNameMakeStructural sig_name) (MkTypArgs pts' cts')
    where
      xtorNameMakeStructural :: XtorName -> XtorName
      xtorNameMakeStructural (MkXtorName _ s) = MkXtorName Structural s

-- | Translate a nominal type into a structural type recursively
translateType :: Typ pol -> TranslateM (Typ pol)
translateType (TyNominal pr tn) = do
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
        xtss <- mapM translateSigArgs $ data_xtors pr
        return $ TyRec pr tv $ TyData pr xtss
      Codata -> do
        xtss <- mapM translateSigArgs $ data_xtors $ flipPolarityRep pr
        return $ TyRec pr tv $ TyCodata pr xtss
translateType tv@TyVar{} = return tv
translateType (TyData pr xtss) = do
  xtss' <- mapM translateSigArgs xtss
  return $ TyData pr xtss'
translateType (TyCodata pr xtss) = do
  xtss' <- mapM translateSigArgs xtss
  return $ TyCodata pr xtss'
translateType TyRefined{} = throwOtherError ["Cannot translate refinement type"]
translateType TyRec{} = throwOtherError ["Cannot translate recursive type"]
translateType TySet{} = throwOtherError ["Cannot translate type set"]

-- | Remove unused recursion headers
cleanUp :: Typ pol -> TranslateM (Typ pol)
cleanUp ty = case ty of
  -- Remove outermost recursive type if its variable is unused
  TyRec pr tv ty' -> do
    s <- gets recVarsUsed
    ty'Cleaned <- cleanUp ty'
    if S.member tv s then return $ TyRec pr tv ty'Cleaned
    else return ty'Cleaned
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
  _ -> throwOtherError ["Nominal type translation: Cleanup error"]
  where
    cleanUpXtorSig :: XtorSig pol -> TranslateM (XtorSig pol)
    cleanUpXtorSig MkXtorSig{..} = do
      pts <- mapM cleanUp $ prdTypes sig_args
      cts <- mapM cleanUp $ cnsTypes sig_args
      return MkXtorSig{ sig_name, sig_args = MkTypArgs pts cts }