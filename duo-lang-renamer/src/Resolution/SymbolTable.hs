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
    ( ResolutionError(OrphanInstance, TypeNameAlreadyUsed,
                      XtorNameAlreadyUsed, FreeVarNameAlreadyUsed, TyOpAlreadyUsed) )
import Syntax.CST.Names
import Syntax.CST.Kinds
import Syntax.CST.Program
import Syntax.CST.Types
import Syntax.RST.Names
import Syntax.RST.Terms qualified as RST
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
  XtorNameResult :: DataCodata ->  RST.NominalStructural -> Arity -> XtorNameResolve
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
  if tn `elem` M.keys st.typeNameMap
  then throwError (TypeNameAlreadyUsed loc tn)
  else pure ()

checkFreshXtorName :: MonadError ResolutionError m
                   => Loc
                   -> XtorName
                   -> SymbolTable
                   -> m ()
checkFreshXtorName loc xt st =
  if xt `elem` M.keys st.xtorNameMap
  then throwError (XtorNameAlreadyUsed loc xt)
  else pure ()

checkFreshFreeVarName :: MonadError ResolutionError m
                   => Loc
                   -> FreeVarName
                   -> SymbolTable
                   -> m ()
checkFreshFreeVarName loc fv st =
  if fv `elem` M.keys st.freeVarMap
  then throwError (FreeVarNameAlreadyUsed loc fv)
  else pure ()

checkFreshTyOpName :: MonadError ResolutionError m
                   => Loc
                   -> TyOpName
                   -> SymbolTable
                   -> m ()
checkFreshTyOpName loc op st =
  if op `elem` M.keys st.tyOps
  then throwError (TyOpAlreadyUsed loc op)
  else pure ()

-- | Creating a symbol table for a program.
-- Throws errors if multiple declarations declare the same name.
createSymbolTable :: MonadError ResolutionError m
                  => Module
                  -> m SymbolTable
createSymbolTable mod = createSymbolTableAcc mod.decls emptySymbolTable
  where
    createSymbolTableAcc [] acc = pure acc
    createSymbolTableAcc (x:xs) acc = do
      acc' <- createSymbolTable' mod.libpath mod.name x acc
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
  checkFreshXtorName decl.loc decl.name st
  let xtorResolve = XtorNameResult decl.data_codata RST.Structural (fst <$> decl.arity)
  pure $ st { xtorNameMap = M.insert decl.name xtorResolve st.xtorNameMap }
createSymbolTable' fp mn  (DataDecl decl) st = do
  -- Check whether the TypeName, and the XtorNames, are already declared in this module
  checkFreshTypeName decl.loc decl.name st
  forM_ ((\sig -> sig.name) <$> decl.xtors) $ \xtorName -> checkFreshXtorName decl.loc xtorName st
  -- Create the default polykind
  let polyKind = case decl.kind of
                    Nothing -> MkPolyKind [] (case decl.data_codata of Data -> CBV; Codata -> CBN)
                    Just knd -> knd
  let ns = case decl.isRefined of
               Refined -> RST.Refinement
               NotRefined -> RST.Nominal decl.name 
  let xtors = M.fromList [(sig.name, XtorNameResult decl.data_codata ns (linearContextToArity sig.args))| sig <- decl.xtors]
  let rnTypeName = MkRnTypeName { rnTnLoc = decl.loc
                                , rnTnDoc = decl.doc
                                , rnTnFp = Just fp
                                , rnTnModule = mn
                                , rnTnName = decl.name
                                }
  let nominalResult = NominalResult rnTypeName decl.data_codata decl.isRefined polyKind
  pure $ st { xtorNameMap = M.union xtors st.xtorNameMap
            , typeNameMap = M.insert decl.name nominalResult st.typeNameMap }
createSymbolTable' _ _ (TyOpDecl decl) st = do
  checkFreshTyOpName decl.loc decl.symbol st
  let descr = MkBinOpDescr { prec = decl.precedence
                           , assoc = decl.associativity
                           , desugar = NominalDesugaring decl.res
                           }
  pure $ st { tyOps = M.insert decl.symbol descr st.tyOps }
createSymbolTable' _ _ (ImportDecl decl) st =
  pure $ st { imports = (decl.mod,decl.loc): st.imports }
createSymbolTable' fp mn (TySynDecl decl) st = do
  -- Check whether the TypeName is already declared in this module
  checkFreshTypeName decl.loc decl.name st
  let rnTypeName = MkRnTypeName { rnTnLoc = decl.loc
                                , rnTnDoc = decl.doc
                                , rnTnFp = Just fp
                                , rnTnModule = mn
                                , rnTnName = decl.name
                                }
  let synonymResult = SynonymResult rnTypeName decl.res
  pure $ st { typeNameMap = M.insert decl.name synonymResult st.typeNameMap }
createSymbolTable' _ _ (PrdCnsDecl decl) st = do
  -- Check if the FreeVarName is already declared in this module
  checkFreshFreeVarName decl.loc decl.name st
  pure $ st { freeVarMap = M.insert decl.name FreeVarResult st.freeVarMap }
createSymbolTable' _ _ (CmdDecl decl) st = do
  checkFreshFreeVarName decl.loc decl.name st
  pure $ st { freeVarMap = M.insert decl.name FreeVarResult st.freeVarMap }
createSymbolTable' _ _ (SetDecl _) st = pure st
createSymbolTable' _ _ (ClassDecl decl)  st = do
  let xtor_names = (\sig -> sig.name) <$> decl.methods
  mapM_ (flip (checkFreshXtorName decl.loc) st) xtor_names
  pure $ st { xtorNameMap = M.union (M.fromList $ zip xtor_names (MethodNameResult decl.name . linearContextToArity . (\sig -> sig.args) <$> decl.methods)) st.xtorNameMap
            , classDecls = S.insert decl.name st.classDecls }
createSymbolTable' _ _ (InstanceDecl decl) st =
  if isPermittedInstance decl.class_name decl.typ st
    then pure st
    else throwError (OrphanInstance decl.loc decl.instance_name decl.class_name decl.typ)
createSymbolTable' _ _ ParseErrorDecl st = pure st

  -- | Check whether the instance declaration would be an orphan instance (neccessary to ensure type class coherence)
  -- Only nominal types and refinement types are allowed.
isPermittedInstance :: ClassName -> Typ -> SymbolTable -> Bool
isPermittedInstance cn ty st = S.member cn st.classDecls || maybe False (`M.member` st.typeNameMap) (getTypeName ty)
  where getTypeName :: Typ -> Maybe TypeName
        getTypeName (TyNominal _ typeName) = Just typeName
        getTypeName (TyXRefined _ _ typeName _ ) = Just typeName
        getTypeName _ = Nothing
