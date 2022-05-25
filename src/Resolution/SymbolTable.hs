module Resolution.SymbolTable where

import Control.Monad.Except
import Data.Map (Map)
import Data.Map qualified as M

import Errors
import Pretty.Pretty
import Pretty.Common ()
import Syntax.Common
import Syntax.CST.Program
import Syntax.Common.TypesUnpol
import Utils

---------------------------------------------------------------------------------
-- Type Operators
---------------------------------------------------------------------------------

data TyOpDesugaring where
    UnionDesugaring :: TyOpDesugaring
    InterDesugaring :: TyOpDesugaring
    NominalDesugaring :: TypeName -> TyOpDesugaring

data TyOp = MkTyOp
    {
        symbol :: BinOp,
        prec :: Precedence,
        assoc :: Associativity,
        desugar :: TyOpDesugaring
    }

---------------------------------------------------------------------------------
-- Symbol Table
---------------------------------------------------------------------------------

-- | What a TypeName can resolve to during name resolution
data TypeNameResolve where
  -- | Typename was introduced in a data or codata declaration
  NominalResult :: RnTypeName -> DataCodata -> IsRefined -> PolyKind -> TypeNameResolve
  -- | TypeName was introduced in a type synonym
  SynonymResult :: RnTypeName -> Typ -> TypeNameResolve

-- | What a XtorName can resolve to during name resolution
data XtorNameResolve where
  -- | Xtor was introduced in a data or codata declaration
  XtorNameResult :: DataCodata ->  NominalStructural -> Arity -> XtorNameResolve

-- | What a toplevel definition can resolve to during name resolution
data FreeVarNameResolve where
  FreeVarResult :: FreeVarNameResolve

data SymbolTable = MkSymbolTable
  { xtorNameMap :: Map XtorName    XtorNameResolve
  , typeNameMap :: Map TypeName    TypeNameResolve
  , freeVarMap  :: Map FreeVarName FreeVarNameResolve
  , tyOps :: [TyOp]
  , imports :: [(ModuleName, Loc)]
  }

emptySymbolTable :: SymbolTable
emptySymbolTable  = MkSymbolTable
    { xtorNameMap = M.empty
    , typeNameMap =  M.empty
    , freeVarMap  = M.empty
    , tyOps       = []
    , imports     = []
    }

instance Show SymbolTable where
  show _ = "<SymbolTable>"

---------------------------------------------------------------------------------
-- Creating a SymbolTable
---------------------------------------------------------------------------------

checkFreshTypeName :: MonadError Error m
                   => Loc
                   -> TypeName
                   -> SymbolTable
                   -> m ()
checkFreshTypeName loc tn st =
  if tn `elem` M.keys (typeNameMap st)
  then throwError (OtherError (Just loc) ("TypeName is already used: " <> ppPrint tn))
  else pure ()

checkFreshXtorName :: MonadError Error m
                   => Loc
                   -> XtorName
                   -> SymbolTable
                   -> m ()
checkFreshXtorName loc xt st =
  if xt `elem` M.keys (xtorNameMap st)
  then throwError (OtherError (Just loc) ("XtorName is already used: " <> ppPrint xt))
  else pure ()

checkFreshFreeVarName :: MonadError Error m
                   => Loc
                   -> FreeVarName
                   -> SymbolTable
                   -> m ()
checkFreshFreeVarName loc fv st =
  if fv `elem` M.keys (freeVarMap st)
  then throwError (OtherError (Just loc) ("FreeVarName is already used: " <> ppPrint fv))
  else pure ()


-- | Creating a symbol table for a program.
-- Throws errors if multiple declarations declare the same name.
createSymbolTable :: MonadError Error m
                  => ModuleName
                  -> Program
                  -> m SymbolTable
createSymbolTable mn prog = createSymbolTableAcc prog emptySymbolTable
  where
    createSymbolTableAcc [] acc = pure acc
    createSymbolTableAcc (x:xs) acc = do
      acc' <- createSymbolTable' mn x acc
      createSymbolTableAcc xs acc'

createSymbolTable' :: MonadError Error m
                   => ModuleName 
                   -> Declaration 
                   -> SymbolTable 
                   -> m SymbolTable
createSymbolTable' _ (XtorDecl loc _ dc xt args _) st = do
  -- Check whether the xtor name is already declared in this module
  checkFreshXtorName loc xt st
  let xtorResolve = XtorNameResult dc Structural (fst <$> args)
  pure $ st { xtorNameMap = M.insert xt xtorResolve (xtorNameMap st)}
createSymbolTable' mn (DataDecl loc doc NominalDecl { data_refined, data_name, data_polarity, data_kind, data_xtors }) st = do
  -- Check whether the TypeName, and the XtorNames, are already declared in this module
  checkFreshTypeName loc data_name st
  forM_ (sig_name <$> data_xtors) $ \xtorName -> checkFreshXtorName loc xtorName st
  -- Create the default polykind
  let polyKind = case data_kind of
                    Nothing -> MkPolyKind [] (case data_polarity of Data -> CBV; Codata -> CBN)
                    Just knd -> knd
  let ns = case data_refined of
               Refined -> Refinement
               NotRefined -> Nominal
  let xtors = M.fromList [(sig_name xt, XtorNameResult data_polarity ns (linearContextToArity (sig_args xt)))| xt <- data_xtors]
  let rnTypeName = MkRnTypeName { rnTnLoc = loc, rnTnDoc = doc, rnTnModule = mn , rnTnName = data_name }
  let nominalResult = NominalResult rnTypeName data_polarity data_refined polyKind
  pure $ st { xtorNameMap = M.union xtors (xtorNameMap st)
            , typeNameMap = M.insert data_name nominalResult (typeNameMap st)}
createSymbolTable' _ (TyOpDecl _ _ op prec assoc ty) st = do
    let tyOp = MkTyOp { symbol = CustomOp op
                      , prec = prec
                      , assoc = assoc
                      , desugar = NominalDesugaring ty
                      }
    pure $ st { tyOps = tyOp : (tyOps st) }
createSymbolTable' _ (ImportDecl loc _ mn) st =
  pure $ st { imports = (mn,loc):(imports st) }
createSymbolTable' mn (TySynDecl loc doc tyname ty) st = do
  -- Check whether the TypeName is already declared in this module
  checkFreshTypeName loc tyname st
  let rnTypeName = MkRnTypeName { rnTnLoc = loc, rnTnDoc = doc, rnTnModule = mn , rnTnName = tyname }
  let synonymResult = SynonymResult rnTypeName ty
  pure $ st { typeNameMap = M.insert tyname synonymResult (typeNameMap st) }
createSymbolTable' _ (PrdCnsDecl loc _ _ _ fv _ _) st = do
  -- Check if the FreeVarName is already declared in this module
  checkFreshFreeVarName loc fv st
  pure $ st { freeVarMap = M.insert fv FreeVarResult (freeVarMap st) }
createSymbolTable' _ (CmdDecl loc _ fv _) st = do
  checkFreshFreeVarName loc fv st
  pure $ st { freeVarMap = M.insert fv FreeVarResult (freeVarMap st) }
createSymbolTable' _ (SetDecl _ _ _) st = pure st
createSymbolTable' _ ParseErrorDecl st = pure st