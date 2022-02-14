module Syntax.Lowering.Lowering (SymbolTable, createSymbolTable, LowerM, LoweringError(..), lowerXtorName, runLowerM, emptySymbolTable) where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text (Text)
import Data.Text qualified as T

import Syntax.CommonTerm
import Syntax.CST.Program
import Syntax.CST.Types
import Syntax.AST.Types (IsRefined(..))

data LoweringError where
    -- Type scheme violations
    MissingVarsInTypeScheme :: LoweringError
    -- Polarity violations
    TopInPosPolarity :: LoweringError
    BotInNegPolarity :: LoweringError
    IntersectionInPosPolarity :: LoweringError
    UnionInNegPolarity :: LoweringError
    -- Operator errors
    UnknownOperator :: BinOp -> LoweringError
    OtherError :: Text -> LoweringError

instance Show LoweringError where
    show MissingVarsInTypeScheme = "Missing declaration of type variable"
    show TopInPosPolarity = "Cannot use `Top` in positive polarity"
    show BotInNegPolarity = "Cannot use `Bot` in negative polarity"
    show IntersectionInPosPolarity = "Cannot use `/\\` in positive polarity"
    show UnionInNegPolarity = "Cannot use `\\/` in negative polarity"
    show (UnknownOperator op) = "Undefined type operator `" ++ show op ++ "`"
    show (OtherError txt) = T.unpack txt

type LowerM a = ReaderT SymbolTable (Except LoweringError) a

runLowerM :: SymbolTable -> LowerM a -> Either LoweringError a
runLowerM st m = runExcept (runReaderT m st)


type SymbolTable = Map XtorName' IsRefined

emptySymbolTable :: SymbolTable
emptySymbolTable = M.empty

createSymbolTable :: Program -> SymbolTable
createSymbolTable decls = go decls M.empty
  where
    go [] acc = acc
    go (decl:decls) acc = go decls (addDecl decl acc)

addDecl :: Declaration -> SymbolTable -> SymbolTable
addDecl (DataDecl _loc NominalDecl { data_refined, data_xtors }) m =
    let
        xtors = sig_name <$> data_xtors
        newm = M.fromList [(xtor, data_refined) | xtor <- xtors]
    in
      M.union m newm
addDecl _ m = m

lowerXtorName :: Bool -> XtorName' -> LowerM XtorName
lowerXtorName True (MkXtorName' xt) = pure (MkXtorName Structural xt)
lowerXtorName _ xtor@(MkXtorName' xt) = do
    st <- ask
    case M.lookup xtor st of
        Nothing -> throwError (OtherError (T.pack ("The symbol" <> show xt <> " is not in symbol table.")))
        Just Refined -> pure (MkXtorName Refinement xt)
        Just NotRefined -> pure (MkXtorName Nominal xt)