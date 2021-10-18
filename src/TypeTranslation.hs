module TypeTranslation where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set
import qualified Data.Set as S

import Errors
import Lookup
import Pretty.Pretty
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
  , recVarsUsed :: Set TVar }

initialState :: TranslateState
initialState = TranslateState { recVarMap = M.empty, recVarsUsed = S.empty }

newtype TranslateReader = TranslateReader { context :: [TypArgs Pos] }

initialReader :: Environment FreeVarName -> (Environment FreeVarName, TranslateReader)
initialReader env = (env, TranslateReader { context = [] })

newtype TranslateM a = TraM { getTraM :: ReaderT (Environment FreeVarName, TranslateReader) (StateT TranslateState (Except Error)) a }
  deriving (Functor, Applicative, Monad, MonadState TranslateState, MonadReader (Environment FreeVarName, TranslateReader), MonadError Error)

runTraM :: Environment FreeVarName -> TranslateM a -> Either Error (a, TranslateState)
runTraM env m = case runExcept (runStateT (runReaderT (getTraM m) (initialReader env)) initialState) of
  Left err -> Left err
  Right (x, state) -> Right (x, state)

---------------------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------------------

modifyVarMap :: (Map TypeName TVar -> Map TypeName TVar) -> TranslateM ()
modifyVarMap f = do
  modify (\TranslateState{..} -> 
    TranslateState{ recVarMap = f recVarMap, recVarsUsed })

modifyVarSet :: (Set TVar -> Set TVar) -> TranslateM ()
modifyVarSet f = do
  modify (\TranslateState{..} ->
    TranslateState{ recVarMap, recVarsUsed = f recVarsUsed })

-- | Translate all producer and consumer types in an xtor signature
translateSigArgs :: XtorSig pol -> TranslateM (XtorSig pol)
translateSigArgs MkXtorSig{..} = do
  pts' <- mapM translateToStructural' $ prdTypes sig_args
  cts' <- mapM translateToStructural' $ cnsTypes sig_args
  return $ MkXtorSig (xtorNameMakeStructural sig_name) (MkTypArgs pts' cts')
    where
      xtorNameMakeStructural :: XtorName -> XtorName
      xtorNameMakeStructural (MkXtorName _ s) = MkXtorName Structural s

-- | Translate a nominal type into a structural type recursively
translateToStructural' :: Typ pol -> TranslateM (Typ pol)
translateToStructural' (TyNominal pr tn) = do
  m <- gets recVarMap
  -- If current type name contained in cache, return corresponding rec. type variable
  if M.member tn m then do
    let tv = fromJust (M.lookup tn m)
    modifyVarSet $ S.insert tv -- add rec. type variable to used var cache
    return $ TyVar pr tv
  else do
    NominalDecl{..} <- lookupTypeName tn
    let tv = MkTVar ("r" <> ppPrint (show 1)) -- TODO: get fresh rec. tvar
    -- Insert current type name into cache with corresponding rec. type variable
    modifyVarMap $ M.insert tn tv
    case data_polarity of
      Data -> do
        xtss <- mapM translateSigArgs $ data_xtors pr
        return $ TyRec pr tv $ TyData pr xtss
      Codata -> do
        xtss <- mapM translateSigArgs $ data_xtors $ flipPolarityRep pr
        return $ TyRec pr tv $ TyCodata pr xtss
translateToStructural' _ = do
  throwOtherError ["Can only translate nominal types"]

-- | Remove unused recursion headers
cleanUp :: Typ pol -> TranslateM (Typ pol)
cleanUp ty = case ty of
  -- Remove outermost recursive type if its variable is unused
  TyRec pr tv ty' -> do
    s <- gets recVarsUsed
    ty'Cleaned <- cleanUp ty'
    if S.member tv s then return $ TyRec pr tv ty'Cleaned
    else return ty'Cleaned
  -- Propagate cleanup in arg types of xtor signature
  TyData pr xtss -> do
    xtss' <- mapM cleanUpXtorSig xtss
    return $ TyData pr xtss'
  -- Propagate cleanup in arg types of xtor signature
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