module TypeTranslation where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as M

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

newtype TranslateState = TranslateState { recVarMap :: Map TypeName TVar }

initialState :: TranslateState
initialState = TranslateState { recVarMap = M.empty }

newtype TranslateReader = TranslateReader { context :: [TypArgs Pos] }

initialReader :: Environment FreeVarName -> (Environment FreeVarName, TranslateReader)
initialReader env = (env, TranslateReader { context = [] })

newtype TraM a = TraM { getTraM :: ReaderT (Environment FreeVarName, TranslateReader) (StateT TranslateState (Except Error)) a }
  deriving (Functor, Applicative, Monad, MonadState TranslateState, MonadReader (Environment FreeVarName, TranslateReader), MonadError Error)

runTraM :: Environment FreeVarName -> TraM a -> Either Error (a, TranslateState)
runTraM env m = case runExcept (runStateT (runReaderT (getTraM m) (initialReader env)) initialState) of
  Left err -> Left err
  Right (x, state) -> Right (x, state)

---------------------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------------------

-- | Make an XtorName structural
xtorNameMakeStructural :: XtorName -> XtorName
xtorNameMakeStructural (MkXtorName _ s) = MkXtorName Structural s

-- | Translate a nominal type into a structural type recursively
translateToStructural' :: Integer -> Typ pol -> TraM (Typ pol)
translateToStructural' i (TyNominal pr tn) = do
  m <- gets recVarMap
  -- If current type name contained in cache, return recursive variable
  if M.member tn m then return $ TyVar pr $ fromJust (M.lookup tn m)
  else do
    NominalDecl{..} <- lookupTypeName tn
    let tv = MkTVar ("r" <> ppPrint (show i))
    case data_polarity of
      Data -> do
        -- let prdts = translateToStructural' (i+1) (M.insert tv tn m) <$> prdTypes . sig_args <$> data_xtors pr
        --
        xtorSig <- forM (data_xtors pr) (\MkXtorSig{..} -> do
            pts' <- mapM (translateToStructural' i) $ prdTypes sig_args
            cts' <- mapM (translateToStructural' i) $ cnsTypes sig_args
            return $ MkXtorSig (xtorNameMakeStructural sig_name) (MkTypArgs pts' cts')
            )
        return $ TyData pr xtorSig
      Codata -> do
        let xtorSig = xtorSigMakeStructural <$> data_xtors (flipPolarityRep pr)
        return $ TyCodata pr xtorSig
translateToStructural' _ _ = do
  throwOtherError ["Can only translate nominal types"]