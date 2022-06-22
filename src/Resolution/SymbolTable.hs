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
data FreeSkolemVarNameResolve where
  FreeSkolemVarResult :: FreeSkolemVarNameResolve

data FreeUniVarNameResolve where
  FreeUniVarResult :: FreeUniVarNameResolve

data SymbolTable = MkSymbolTable
  { xtorNameMap :: Map XtorName    XtorNameResolve
  , typeNameMap :: Map TypeName    TypeNameResolve
  , freeSkolemVarMap  :: Map FreeSkolemVarName FreeSkolemVarNameResolve
  , freeUniVarMap :: Map FreeUniVarName FreeUniVarNameResolve
  , tyOps :: [TyOp]
  , imports :: [(ModuleName, Loc)]
  }

emptySymbolTable :: SymbolTable
emptySymbolTable  = MkSymbolTable
    { xtorNameMap = M.empty
    , typeNameMap =  M.empty
    , freeSkolemVarMap  = M.empty
    , freeUniVarMap = M.empty
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

checkFreshFreeSkolemVarName :: MonadError Error m
                   => Loc
                   -> FreeSkolemVarName
                   -> SymbolTable
                   -> m ()
checkFreshFreeSkolemVarName loc fv st =
  if fv `elem` M.keys (freeSkolemVarMap st)
  then throwError (OtherError (Just loc) ("FreeSkolemVarName is already used: " <> ppPrint fv))
  else pure ()

checkFreshFreeUniVarName :: MonadError Error m
                   => Loc
                   -> FreeUniVarName
                   -> SymbolTable
                   -> m ()
checkFreshFreeUniVarName loc fv st =
  if fv `elem` M.keys (freeUniVarMap st)
  then throwError (OtherError (Just loc) ("FreeUniVarName is already used: " <> ppPrint fv))
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
createSymbolTable' _ (XtorDecl MkStructuralXtorDeclaration {strxtordecl_loc, strxtordecl_xdata, strxtordecl_name, strxtordecl_arity }) st = do
  -- Check whether the xtor name is already declared in this module
  checkFreshXtorName strxtordecl_loc strxtordecl_name st
  let xtorResolve = XtorNameResult strxtordecl_xdata Structural (fst <$> strxtordecl_arity)
  pure $ st { xtorNameMap = M.insert strxtordecl_name xtorResolve (xtorNameMap st)}
createSymbolTable' mn (DataDecl NominalDecl { data_loc, data_doc, data_refined, data_name, data_polarity, data_kind, data_xtors }) st = do
  -- Check whether the TypeName, and the XtorNames, are already declared in this module
  checkFreshTypeName data_loc data_name st
  forM_ (sig_name <$> data_xtors) $ \xtorName -> checkFreshXtorName data_loc xtorName st
  -- Create the default polykind
  let polyKind = case data_kind of
                    Nothing -> MkPolyKind [] (case data_polarity of Data -> CBV; Codata -> CBN)
                    Just knd -> knd
  let ns = case data_refined of
               Refined -> Refinement
               NotRefined -> Nominal
  let xtors = M.fromList [(sig_name xt, XtorNameResult data_polarity ns (linearContextToArity (sig_args xt)))| xt <- data_xtors]
  let rnTypeName = MkRnTypeName { rnTnLoc = data_loc, rnTnDoc = data_doc, rnTnModule = mn , rnTnName = data_name }
  let nominalResult = NominalResult rnTypeName data_polarity data_refined polyKind
  pure $ st { xtorNameMap = M.union xtors (xtorNameMap st)
            , typeNameMap = M.insert data_name nominalResult (typeNameMap st)}
createSymbolTable' _ (TyOpDecl MkTyOpDeclaration { tyopdecl_sym, tyopdecl_prec, tyopdecl_assoc, tyopdecl_res}) st = do
    let tyOp = MkTyOp { symbol = CustomOp tyopdecl_sym
                      , prec = tyopdecl_prec
                      , assoc = tyopdecl_assoc
                      , desugar = NominalDesugaring tyopdecl_res
                      }
    pure $ st { tyOps = tyOp : tyOps st }
createSymbolTable' _ (ImportDecl MkImportDeclaration { imprtdecl_loc, imprtdecl_module }) st =
  pure $ st { imports = (imprtdecl_module,imprtdecl_loc):imports st }
createSymbolTable' mn (TySynDecl MkTySynDeclaration { tysyndecl_loc, tysyndecl_doc, tysyndecl_name, tysyndecl_res }) st = do
  -- Check whether the TypeName is already declared in this module
  checkFreshTypeName tysyndecl_loc tysyndecl_name st
  let rnTypeName = MkRnTypeName { rnTnLoc = tysyndecl_loc, rnTnDoc = tysyndecl_doc, rnTnModule = mn , rnTnName = tysyndecl_name }
  let synonymResult = SynonymResult rnTypeName tysyndecl_res
  pure $ st { typeNameMap = M.insert tysyndecl_name synonymResult (typeNameMap st) }
createSymbolTable' _ (PrdCnsDecl MkPrdCnsDeclaration { pcdecl_loc, pcdecl_name }) st = do
  -- Check if the FreeVarName is already declared in this module
  checkFreshFreeSkolemVarName pcdecl_loc pcdecl_name st
  pure $ st { freeSkolemVarMap = M.insert pcdecl_name FreeSkolemVarResult (freeSkolemVarMap st) }
createSymbolTable' _ (CmdDecl MkCommandDeclaration { cmddecl_loc, cmddecl_name }) st = do
  checkFreshFreeSkolemVarName cmddecl_loc cmddecl_name st
  pure $ st { freeSkolemVarMap = M.insert cmddecl_name FreeSkolemVarResult (freeSkolemVarMap st) }
createSymbolTable' _ (SetDecl _) st = pure st
createSymbolTable' _ ParseErrorDecl st = pure st
