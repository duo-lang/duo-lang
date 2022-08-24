module Resolution.SymbolTable
  ( BinOpDescr(..)
  , TyOpDesugaring(..)
  , TypeNameResolve(..)
  , XtorNameResolve(..)
  , SymbolTable(..)
  , createSymbolTable
  ) where

import Control.Monad.Except
import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import Data.Map qualified as M

import Errors
import Pretty.Pretty
import Pretty.Common ()
import Syntax.CST.Names
import Syntax.CST.Kinds
import Syntax.CST.Program
import Syntax.CST.Types
import Syntax.CST.Terms
import Utils

---------------------------------------------------------------------------------
-- Binary Type Operators
---------------------------------------------------------------------------------

data TyOpDesugaring where
    UnionDesugaring :: TyOpDesugaring
    InterDesugaring :: TyOpDesugaring
    NominalDesugaring :: TypeName -> TyOpDesugaring

data BinOpDescr = MkBinOpDescr
    { prec :: Precedence,
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
  -- | Xtor was introduced as a method in a class declaration
  MethodNameResult :: ClassName -> Arity -> XtorNameResolve

-- | What a toplevel definition can resolve to during name resolution
data FreeVarNameResolve where
  FreeVarResult :: FreeVarNameResolve

data SymbolTable = MkSymbolTable
  { xtorNameMap  :: Map XtorName XtorNameResolve
  , typeNameMap  :: Map TypeName TypeNameResolve
  , freeVarMap   :: Map FreeVarName FreeVarNameResolve
  , tyOps        :: Map TyOpName BinOpDescr
  , imports      :: [(ModuleName, Loc)]
  }

emptySymbolTable :: SymbolTable
emptySymbolTable = MkSymbolTable { xtorNameMap  = M.empty
                                 , typeNameMap  = M.empty
                                 , freeVarMap   = M.empty
                                 , tyOps        = M.empty
                                 , imports      = []
                                 }

instance Show SymbolTable where
  show _ = "<SymbolTable>"

---------------------------------------------------------------------------------
-- Creating a SymbolTable
---------------------------------------------------------------------------------

checkFreshTypeName :: MonadError (NonEmpty Error) m
                   => Loc
                   -> TypeName
                   -> SymbolTable
                   -> m ()
checkFreshTypeName loc tn st =
  if tn `elem` M.keys (typeNameMap st)
  then throwOtherError loc ["TypeName is already used: " <> ppPrint tn]
  else pure ()

checkFreshXtorName :: MonadError (NonEmpty Error) m
                   => Loc
                   -> XtorName
                   -> SymbolTable
                   -> m ()
checkFreshXtorName loc xt st =
  if xt `elem` M.keys (xtorNameMap st)
  then throwOtherError loc ["XtorName is already used: " <> ppPrint xt]
  else pure ()

checkFreshFreeVarName :: MonadError (NonEmpty Error) m
                   => Loc
                   -> FreeVarName
                   -> SymbolTable
                   -> m ()
checkFreshFreeVarName loc fv st =
  if fv `elem` M.keys (freeVarMap st)
  then throwOtherError loc ["FreeVarName is already used: " <> ppPrint fv]
  else pure ()

-- | Creating a symbol table for a program.
-- Throws errors if multiple declarations declare the same name.
createSymbolTable :: MonadError (NonEmpty Error) m
                  => Module
                  -> m SymbolTable
createSymbolTable MkModule { mod_name, mod_fp, mod_decls } = createSymbolTableAcc mod_decls emptySymbolTable
  where
    createSymbolTableAcc [] acc = pure acc
    createSymbolTableAcc (x:xs) acc = do
      acc' <- createSymbolTable' mod_fp mod_name x acc
      createSymbolTableAcc xs acc'

createSymbolTable' :: MonadError (NonEmpty Error) m
                   => FilePath
                   -> ModuleName
                      -- ^ FilePath and ModuleName of the module for which the symbol table is created
                   -> Declaration
                   -> SymbolTable
                   -> m SymbolTable
createSymbolTable' _ _ (XtorDecl MkStructuralXtorDeclaration {strxtordecl_loc, strxtordecl_xdata, strxtordecl_name, strxtordecl_arity }) st = do
  -- Check whether the xtor name is already declared in this module
  checkFreshXtorName strxtordecl_loc strxtordecl_name st
  let xtorResolve = XtorNameResult strxtordecl_xdata Structural (fst <$> strxtordecl_arity)
  pure $ st { xtorNameMap = M.insert strxtordecl_name xtorResolve (xtorNameMap st)}
createSymbolTable' fp mn  (DataDecl MkDataDecl { data_loc, data_doc, data_refined, data_name, data_polarity, data_kind, data_xtors }) st = do
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
  let rnTypeName = MkRnTypeName { rnTnLoc = data_loc
                                , rnTnDoc = data_doc
                                , rnTnFp = Just fp
                                , rnTnModule = mn
                                , rnTnName = data_name
                                }
  let nominalResult = NominalResult rnTypeName data_polarity data_refined polyKind
  pure $ st { xtorNameMap = M.union xtors (xtorNameMap st)
            , typeNameMap = M.insert data_name nominalResult (typeNameMap st)}
createSymbolTable' _ _ (TyOpDecl MkTyOpDeclaration { tyopdecl_sym, tyopdecl_prec, tyopdecl_assoc, tyopdecl_res}) st = do
  let descr = MkBinOpDescr { prec = tyopdecl_prec
                           , assoc = tyopdecl_assoc
                           , desugar = NominalDesugaring tyopdecl_res
                           }
  pure $ st { tyOps = M.insert tyopdecl_sym descr (tyOps st) }
createSymbolTable' _ _ (ImportDecl MkImportDeclaration { imprtdecl_loc, imprtdecl_module }) st =
  pure $ st { imports = (imprtdecl_module,imprtdecl_loc):imports st }
createSymbolTable' fp mn (TySynDecl MkTySynDeclaration { tysyndecl_loc, tysyndecl_doc, tysyndecl_name, tysyndecl_res }) st = do
  -- Check whether the TypeName is already declared in this module
  checkFreshTypeName tysyndecl_loc tysyndecl_name st
  let rnTypeName = MkRnTypeName { rnTnLoc = tysyndecl_loc
                                , rnTnDoc = tysyndecl_doc
                                , rnTnFp = Just fp
                                , rnTnModule = mn
                                , rnTnName = tysyndecl_name
                                }
  let synonymResult = SynonymResult rnTypeName tysyndecl_res
  pure $ st { typeNameMap = M.insert tysyndecl_name synonymResult (typeNameMap st) }
createSymbolTable' _ _ (PrdCnsDecl MkPrdCnsDeclaration { pcdecl_loc, pcdecl_name }) st = do
  -- Check if the FreeVarName is already declared in this module
  checkFreshFreeVarName pcdecl_loc pcdecl_name st
  pure $ st { freeVarMap = M.insert pcdecl_name FreeVarResult (freeVarMap st) }
createSymbolTable' _ _ (CmdDecl MkCommandDeclaration { cmddecl_loc, cmddecl_name }) st = do
  checkFreshFreeVarName cmddecl_loc cmddecl_name st
  pure $ st { freeVarMap = M.insert cmddecl_name FreeVarResult (freeVarMap st) }
createSymbolTable' _ _ (SetDecl _) st = pure st
createSymbolTable' _ _ (ClassDecl MkClassDeclaration {classdecl_loc, classdecl_name, classdecl_methods})  st = do
  let xtor_names = sig_name <$> classdecl_methods
  mapM_ (flip (checkFreshXtorName classdecl_loc) st) xtor_names
  pure $ st { xtorNameMap = M.union (M.fromList $ zip xtor_names (MethodNameResult classdecl_name . linearContextToArity . sig_args <$> classdecl_methods)) (xtorNameMap st) }
createSymbolTable' _ _ InstanceDecl {} st = pure st
createSymbolTable' _ _ ParseErrorDecl st = pure st
