module Driver.Environment where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Map (Map)
import Data.Map qualified as M
import Data.List ( find )
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty qualified as NE
import Data.Set (Set)

import Errors
import Pretty.Types ()
import Pretty.Pretty
import Syntax.CST.Names
import Syntax.TST.Terms ( Command, Term )
import Syntax.RST.Program ( ClassDeclaration (..), StructuralXtorDeclaration, PrdCnsToPol )
import Syntax.TST.Types ( TypeScheme, Typ, XtorSig(..) )
import Syntax.TST.Program ( DataDecl(..), InstanceDeclaration )
import Syntax.RST.Types (Polarity(..), PolarityRep(..), MethodSig (..), LinearContext)
import Syntax.CST.Types( PrdCns(..), PrdCnsRep(..))
import Syntax.CST.Kinds (EvaluationOrder)
import Loc ( Loc, defaultLoc )
import qualified Syntax.RST.Program as RST

---------------------------------------------------------------------------------
-- Environment
---------------------------------------------------------------------------------

data Environment = MkEnvironment
  { prdEnv :: Map FreeVarName (Term Prd, Loc, TypeScheme Pos)
  , cnsEnv :: Map FreeVarName (Term Cns, Loc, TypeScheme Neg)
  , cmdEnv :: Map FreeVarName (Command, Loc)
  , classEnv :: Map ClassName ClassDeclaration
  , instanceDeclEnv :: Map FreeVarName InstanceDeclaration
  , instanceEnv :: Map ClassName (Set (FreeVarName, Typ Pos, Typ Neg))
  , declEnv :: [(Loc,DataDecl)]
  , kindEnv :: Map XtorName EvaluationOrder -- for each xtructor a return kind 
  , xtorEnv :: Map XtorName StructuralXtorDeclaration
  }

emptyEnvironment :: Environment
emptyEnvironment = MkEnvironment M.empty M.empty M.empty M.empty M.empty M.empty [] M.empty M.empty
instance Show Environment where
  show :: Environment -> String
  show _ = "<Environment>"

---------------------------------------------------------------------------------
-- We define functions which work for every Monad which implements:
-- (1) MonadError Error
-- (2) MonadReader (Map ModuleName Environment ph, a)
---------------------------------------------------------------------------------

type EnvReader a m = (MonadError (NonEmpty Error) m, MonadReader (Map ModuleName Environment, a) m)

---------------------------------------------------------------------------------
-- Lookup Terms
---------------------------------------------------------------------------------

findFirstM :: forall a m res. EnvReader a m
           => (Environment -> Maybe res)
           -> Error
           -> m (ModuleName, res)
findFirstM f err = asks fst >>= \env -> go (M.toList env)
  where
    go :: [(ModuleName, Environment)] -> m (ModuleName, res)
    go [] = throwError (err NE.:| [])
    go ((mn,env):envs) =
      case f env of
        Just res -> pure (mn,res)
        Nothing -> go envs

-- | Lookup the term and the type of a term bound in the environment.
lookupTerm :: EnvReader a m => Loc -> PrdCnsRep pc -> FreeVarName -> m (Term pc, TypeScheme (PrdCnsToPol pc))
lookupTerm loc PrdRep fv = do
  env <- asks fst
  let err = ErrOther $ SomeOtherError loc ("Unbound free producer variable " <> ppPrint fv <> " is not contained in environment.\n" <> ppPrint (M.keys env))
  let f env = case M.lookup fv (prdEnv env) of
                       Nothing -> Nothing
                       Just (res1,_,res2) -> Just (res1,res2)
  snd <$> findFirstM f err
lookupTerm loc CnsRep fv = do
  let err = ErrOther $ SomeOtherError loc ("Unbound free consumer variable " <> ppPrint fv <> " is not contained in environment.")
  let f env = case M.lookup fv (cnsEnv env) of
                       Nothing -> Nothing
                       Just (res1,_,res2) -> return (res1,res2)
  snd <$> findFirstM f err

---------------------------------------------------------------------------------
-- Lookup Commands
---------------------------------------------------------------------------------

-- | Lookup a command in the environment.
lookupCommand :: EnvReader a m => Loc -> FreeVarName -> m Command
lookupCommand loc fv = do
  let err = ErrOther $ SomeOtherError loc ("Unbound free command variable " <> ppPrint fv <> " is not contained in environment.")
  let f env = case M.lookup fv (cmdEnv env) of
                     Nothing -> Nothing
                     Just (res, _) -> return res
  snd <$> findFirstM f err

---------------------------------------------------------------------------------
-- Lookup information about type declarations ------------------------------------------------------------------------------- | Find the type declaration belonging to a given Xtor Name.
lookupDataDecl :: EnvReader a m
               => Loc -> XtorName -> m DataDecl
lookupDataDecl loc xt = do
  let containsXtor :: XtorSig Pos -> Bool
      containsXtor sig = sig_name sig == xt
  let typeContainsXtor :: DataDecl -> Bool
      typeContainsXtor NominalDecl { data_xtors } | or (containsXtor <$> fst data_xtors) = True
                                                      | otherwise = False
      typeContainsXtor RefinementDecl { data_xtors } | or (containsXtor <$> fst data_xtors) = True
                                                         | otherwise = False
  let err = ErrOther $ SomeOtherError loc ("Constructor/Destructor " <> ppPrint xt <> " is not contained in program.")
  let f env = find typeContainsXtor (fmap snd (declEnv env))
  snd <$> findFirstM f err

-- | Find the type declaration belonging to a given TypeName.
lookupTypeName :: EnvReader a m
               => Loc -> RnTypeName -> m DataDecl
lookupTypeName loc tn = do
  let err = ErrOther $ SomeOtherError loc ("Type name " <> unTypeName (rnTnName tn) <> " not found in environment")
  let findFun NominalDecl{..} = data_name == tn
      findFun RefinementDecl {..} = data_name == tn
  let f env = find findFun (fmap snd (declEnv env))
  snd <$> findFirstM f err

-- | Find the XtorSig belonging to a given XtorName.
lookupXtorSig :: EnvReader a m
              => Loc -> XtorName -> PolarityRep pol -> m (XtorSig pol)
lookupXtorSig loc xtn PosRep = do
  decl <- lookupDataDecl loc xtn
  case find ( \MkXtorSig{..} -> sig_name == xtn ) (fst (data_xtors decl)) of
    Just xts -> pure xts
    Nothing -> throwOtherError loc ["XtorName " <> unXtorName xtn <> " not found in declaration of type " <> unTypeName (rnTnName (data_name decl))]
lookupXtorSig loc xtn NegRep = do
  decl <- lookupDataDecl loc xtn
  case find ( \MkXtorSig{..} -> sig_name == xtn ) (snd (data_xtors decl)) of
    Just xts -> pure xts
    Nothing -> throwOtherError loc ["XtorName " <> unXtorName xtn <> " not found in declaration of type " <> unTypeName (rnTnName (data_name decl))]


lookupXtorSigUpper :: EnvReader a m
                   => Loc -> XtorName -> m (XtorSig Neg)
lookupXtorSigUpper loc xt = do
  decl <- lookupDataDecl loc xt
  case decl of
    NominalDecl { } -> do
      throwOtherError loc ["lookupXtorSigUpper: Expected refinement type but found nominal type."]
    RefinementDecl { data_xtors_refined } -> do
      case find ( \MkXtorSig{..} -> sig_name == xt ) (snd data_xtors_refined) of
        Nothing -> throwOtherError loc ["lookupXtorSigUpper: Constructor/Destructor " <> ppPrint xt <> " not found"]
        Just sig -> pure sig



lookupXtorSigLower :: EnvReader a m
                   => Loc -> XtorName -> m (XtorSig Pos)
lookupXtorSigLower loc xt = do
  decl <- lookupDataDecl loc xt
  case decl of
    NominalDecl {} -> do
      throwOtherError loc ["lookupXtorSigLower: Expected refinement type but found nominal type."]
    RefinementDecl { data_xtors_refined } -> do
      case find ( \MkXtorSig{..} -> sig_name == xt ) (fst data_xtors_refined) of
        Nothing ->  throwOtherError loc ["lookupXtorSigLower: Constructor/Destructor " <> ppPrint xt <> " not found"]
        Just sig -> pure sig



-- | Find the class declaration for a classname.
lookupClassDecl :: EnvReader a m
               => Loc -> ClassName -> m ClassDeclaration
lookupClassDecl loc cn = do
  let err = ErrOther $ SomeOtherError loc ("Undeclared class " <> ppPrint cn <> " is not contained in environment.")
  let f env = M.lookup cn (classEnv env)
  snd <$> findFirstM f err

-- | Find the type of a method in a given class declaration.
lookupMethodType :: EnvReader a m
               => Loc -> MethodName -> ClassDeclaration -> PolarityRep pol -> m (LinearContext pol)
lookupMethodType loc mn MkClassDeclaration { classdecl_name, classdecl_methods } PosRep =
  case find ( \MkMethodSig{..} -> msig_name == mn) (fst classdecl_methods) of
    Nothing -> throwOtherError loc ["Method " <> ppPrint mn <> " is not declared in class " <> ppPrint classdecl_name]
    Just msig -> pure $ msig_args msig
lookupMethodType loc mn MkClassDeclaration { classdecl_name, classdecl_methods } NegRep =
  case find ( \MkMethodSig{..} -> msig_name == mn) (snd classdecl_methods) of
    Nothing -> throwOtherError loc ["Method " <> ppPrint mn <> " is not declared in class " <> ppPrint classdecl_name]
    Just msig -> pure $ msig_args msig

lookupXtorKind :: EnvReader a m
             => XtorName -> m EvaluationOrder
lookupXtorKind xtorn = do
  let err = ErrOther $ SomeOtherError defaultLoc ("No Kinds for XTor " <> ppPrint xtorn)
  let f env = M.lookup xtorn (kindEnv env)
  snd <$> findFirstM f err


lookupStructuralXtor :: EnvReader a m
                => XtorName -> m RST.StructuralXtorDeclaration
lookupStructuralXtor xtorn = do 
  let err = ErrOther $ SomeOtherError defaultLoc ("Xtor " <> ppPrint xtorn <> " not found in program")
  let f env = M.lookup xtorn (xtorEnv env)
  snd <$> findFirstM f err

---------------------------------------------------------------------------------
-- Run a computation in a locally changed environment.
---------------------------------------------------------------------------------

withTerm :: forall a m b pc. EnvReader a m
         => ModuleName -> PrdCnsRep pc -> FreeVarName -> Term pc -> Loc -> TypeScheme (PrdCnsToPol pc)
         -> (m b -> m b)
withTerm mn PrdRep fv tm loc tys action = do
  let modifyEnv :: Environment -> Environment
      modifyEnv env@MkEnvironment { prdEnv } =
        env { prdEnv = M.insert fv (tm,loc,tys) prdEnv }
  let modifyEnvMap :: (Map ModuleName Environment, a) -> (Map ModuleName Environment, a)
      modifyEnvMap (map, rest) =
        case M.lookup mn map of
          Nothing -> (M.insert mn (modifyEnv emptyEnvironment) map, rest)
          Just _  -> (M.adjust modifyEnv mn map, rest)
  local modifyEnvMap action
withTerm mn CnsRep fv tm loc tys action = do
  let modifyEnv :: Environment -> Environment
      modifyEnv env@MkEnvironment { cnsEnv } =
        env { cnsEnv = M.insert fv (tm,loc,tys) cnsEnv }
  let modifyEnvMap :: (Map ModuleName Environment, a) -> (Map ModuleName Environment, a)
      modifyEnvMap (map, rest) =
        case M.lookup mn map of
          Nothing ->  (M.insert mn (modifyEnv emptyEnvironment) map, rest)
          Just _  -> (M.adjust modifyEnv mn map, rest)
  local modifyEnvMap action

