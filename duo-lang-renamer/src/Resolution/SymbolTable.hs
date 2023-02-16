module Resolution.SymbolTable
  ( BinOpDescr(..)
  , TyOpDesugaring(..)
  , TypeNameResolve(..)
  , XtorNameResolve(..)
  , SymbolTable(..)
  , createSymbolTable
  ) where

import Control.Monad.Except
import Data.Map (Map)
import Data.Set (Set)
import Data.Map qualified as M
import Data.Set qualified as S

import Errors.Renamer
import Syntax.CST.Names
import Syntax.CST.Kinds
import Syntax.CST.Program
import Syntax.CST.Types
import Syntax.CST.Terms
import Loc ( Loc )

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
  , classDecls   :: Set ClassName
  , imports      :: [(ModuleName, Loc)]
  }

emptySymbolTable :: SymbolTable
emptySymbolTable = MkSymbolTable { xtorNameMap  = M.empty
                                 , typeNameMap  = M.empty
                                 , freeVarMap   = M.empty
                                 , tyOps        = M.empty
                                 , classDecls   = S.empty
                                 , imports      = []
                                 }

instance Show SymbolTable where
  show _ = "<SymbolTable>"

---------------------------------------------------------------------------------
-- Creating a SymbolTable
---------------------------------------------------------------------------------

checkFreshTypeName :: MonadError ResolutionError m
                   => Loc
                   -> TypeName
                   -> SymbolTable
                   -> m ()
checkFreshTypeName loc tn st =
  if tn `elem` M.keys (typeNameMap st)
  then throwError (TypeNameAlreadyUsed loc tn)
  else pure ()

checkFreshXtorName :: MonadError ResolutionError m
                   => Loc
                   -> XtorName
                   -> SymbolTable
                   -> m ()
checkFreshXtorName loc xt st =
  if xt `elem` M.keys (xtorNameMap st)
  then throwError (XtorNameAlreadyUsed loc xt)
  else pure ()

checkFreshFreeVarName :: MonadError ResolutionError m
                   => Loc
                   -> FreeVarName
                   -> SymbolTable
                   -> m ()
checkFreshFreeVarName loc fv st =
  if fv `elem` M.keys (freeVarMap st)
  then throwError (FreeVarNameAlreadyUsed loc fv)
  else pure ()

checkFreshTyOpName :: MonadError ResolutionError m
                   => Loc
                   -> TyOpName
                   -> SymbolTable
                   -> m ()
checkFreshTyOpName loc op st =
  if op `elem` M.keys (tyOps st)
  then throwError (TyOpAlreadyUsed loc op)
  else pure ()

-- | Creating a symbol table for a program.
-- Throws errors if multiple declarations declare the same name.
createSymbolTable :: MonadError ResolutionError m
                  => Module
                  -> m SymbolTable
createSymbolTable mod = createSymbolTableAcc mod.mod_decls emptySymbolTable
  where
    createSymbolTableAcc [] acc = pure acc
    createSymbolTableAcc (x:xs) acc = do
      acc' <- createSymbolTable' mod.mod_libpath mod.mod_name x acc
      createSymbolTableAcc xs acc'

createSymbolTable' :: MonadError ResolutionError m
                   => FilePath
                   -> ModuleName
                      -- ^ FilePath and ModuleName of the module for which the symbol table is created
                   -> Declaration
                   -> SymbolTable
                   -> m SymbolTable
createSymbolTable' _ _ (XtorDecl decl) st = do
  -- Check whether the xtor name is already declared in this module
  checkFreshXtorName decl.strxtordecl_loc decl.strxtordecl_name st
  let xtorResolve = XtorNameResult decl.strxtordecl_xdata Structural (fst <$> decl.strxtordecl_arity)
  pure $ st { xtorNameMap = M.insert decl.strxtordecl_name xtorResolve (xtorNameMap st)}
createSymbolTable' fp mn  (DataDecl decl) st = do
  -- Check whether the TypeName, and the XtorNames, are already declared in this module
  checkFreshTypeName decl.data_loc decl.data_name st
  forM_ (sig_name <$> decl.data_xtors) $ \xtorName -> checkFreshXtorName decl.data_loc xtorName st
  -- Create the default polykind
  let polyKind = case decl.data_kind of
                    Nothing -> MkPolyKind [] (case decl.data_polarity of Data -> CBV; Codata -> CBN)
                    Just knd -> knd
  let ns = case decl.data_refined of
               Refined -> Refinement
               NotRefined -> Nominal
  let xtors = M.fromList [(sig_name xt, XtorNameResult decl.data_polarity ns (linearContextToArity (sig_args xt)))| xt <- decl.data_xtors]
  let rnTypeName = MkRnTypeName { rnTnLoc = decl.data_loc
                                , rnTnDoc = decl.data_doc
                                , rnTnFp = Just fp
                                , rnTnModule = mn
                                , rnTnName = decl.data_name
                                }
  let nominalResult = NominalResult rnTypeName decl.data_polarity decl.data_refined polyKind
  pure $ st { xtorNameMap = M.union xtors (xtorNameMap st)
            , typeNameMap = M.insert decl.data_name nominalResult (typeNameMap st)}
createSymbolTable' _ _ (TyOpDecl decl) st = do
  checkFreshTyOpName decl.tyopdecl_loc decl.tyopdecl_sym st
  let descr = MkBinOpDescr { prec = decl.tyopdecl_prec
                           , assoc = decl.tyopdecl_assoc
                           , desugar = NominalDesugaring decl.tyopdecl_res
                           }
  pure $ st { tyOps = M.insert decl.tyopdecl_sym descr (tyOps st) }
createSymbolTable' _ _ (ImportDecl decl) st =
  pure $ st { imports = (decl.imprtdecl_module,decl.imprtdecl_loc):imports st }
createSymbolTable' fp mn (TySynDecl decl) st = do
  -- Check whether the TypeName is already declared in this module
  checkFreshTypeName decl.tysyndecl_loc decl.tysyndecl_name st
  let rnTypeName = MkRnTypeName { rnTnLoc = decl.tysyndecl_loc
                                , rnTnDoc = decl.tysyndecl_doc
                                , rnTnFp = Just fp
                                , rnTnModule = mn
                                , rnTnName = decl.tysyndecl_name
                                }
  let synonymResult = SynonymResult rnTypeName decl.tysyndecl_res
  pure $ st { typeNameMap = M.insert decl.tysyndecl_name synonymResult (typeNameMap st) }
createSymbolTable' _ _ (PrdCnsDecl decl) st = do
  -- Check if the FreeVarName is already declared in this module
  checkFreshFreeVarName decl.pcdecl_loc decl.pcdecl_name st
  pure $ st { freeVarMap = M.insert decl.pcdecl_name FreeVarResult (freeVarMap st) }
createSymbolTable' _ _ (CmdDecl decl) st = do
  checkFreshFreeVarName decl.cmddecl_loc decl.cmddecl_name st
  pure $ st { freeVarMap = M.insert decl.cmddecl_name FreeVarResult (freeVarMap st) }
createSymbolTable' _ _ (SetDecl _) st = pure st
createSymbolTable' _ _ (ClassDecl decl)  st = do
  let xtor_names = sig_name <$> decl.classdecl_methods
  mapM_ (flip (checkFreshXtorName decl.classdecl_loc) st) xtor_names
  pure $ st { xtorNameMap = M.union (M.fromList $ zip xtor_names (MethodNameResult decl.classdecl_name . linearContextToArity . sig_args <$> decl.classdecl_methods)) (xtorNameMap st)
            , classDecls = S.insert decl.classdecl_name (classDecls st) }
createSymbolTable' _ _ (InstanceDecl decl) st =
  if isPermittedInstance decl.instancedecl_class decl.instancedecl_typ st
    then pure st
    else throwError (OrphanInstance decl.instancedecl_loc decl.instancedecl_name decl.instancedecl_class decl.instancedecl_typ)
createSymbolTable' _ _ ParseErrorDecl st = pure st

  -- | Check whether the instance declaration would be an orphan instance (neccessary to ensure type class coherence)
  -- Only nominal types and refinement types are allowed.
isPermittedInstance :: ClassName -> Typ -> SymbolTable -> Bool
isPermittedInstance cn ty st = S.member cn (classDecls st) || maybe False (`M.member` typeNameMap st) (getTypeName ty)
  where getTypeName :: Typ -> Maybe TypeName
        getTypeName (TyNominal _ typeName) = Just typeName
        getTypeName (TyXRefined _ _ typeName _ _) = Just typeName
        getTypeName _ = Nothing
