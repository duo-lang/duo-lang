module TypeInference.Environment where

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
import Syntax.CST.Types (EvaluationOrder,PolyKind(..))
import Syntax.RST.Names
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
  , xtorEnv :: Map XtorName StructuralXtorDeclaration
  }

emptyEnvironment :: Environment
emptyEnvironment = MkEnvironment M.empty M.empty M.empty M.empty M.empty M.empty [] M.empty
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
  let f env = case M.lookup fv env.prdEnv of
                       Nothing -> Nothing
                       Just (res1,_,res2) -> Just (res1,res2)
  snd <$> findFirstM f err
lookupTerm loc CnsRep fv = do
  let err = ErrOther $ SomeOtherError loc ("Unbound free consumer variable " <> ppPrint fv <> " is not contained in environment.")
  let f env = case M.lookup fv env.cnsEnv of
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
  let f env = case M.lookup fv env.cmdEnv of
                     Nothing -> Nothing
                     Just (res, _) -> return res
  snd <$> findFirstM f err

---------------------------------------------------------------------------------
-- Lookup information about type declarations ------------------------------------------------------------------------------- | Find the type declaration belonging to a given Xtor Name.
lookupDataDecl :: EnvReader a m
               => Loc -> XtorName -> m DataDecl
lookupDataDecl loc xt = do
  let containsXtor :: XtorSig Pos -> Bool
      containsXtor sig = sig.sig_name == xt
  let typeContainsXtor :: DataDecl -> Bool
      typeContainsXtor decl@NominalDecl {} | or (containsXtor <$> fst decl.data_xtors) = True
                                                      | otherwise = False
      typeContainsXtor decl@RefinementDecl {} | or (containsXtor <$> fst decl.data_xtors) = True
                                                      | otherwise = False
  let err = ErrOther $ SomeOtherError loc ("Constructor/Destructor " <> ppPrint xt <> " is not contained in program.")
  let f env = find typeContainsXtor (fmap snd env.declEnv)
  snd <$> findFirstM f err

-- | Find the type declaration belonging to a given TypeName.
lookupTypeName :: EnvReader a m
               => Loc -> RnTypeName -> m DataDecl
lookupTypeName loc tn = do
  let err = ErrOther $ SomeOtherError loc ("Type name " <> tn.rnTnName.unTypeName <> " not found in environment")
  let findFun decl@NominalDecl{} = decl.data_name == tn
      findFun decl@RefinementDecl {} = decl.data_name == tn
  let f env = find findFun (fmap snd env.declEnv)
  snd <$> findFirstM f err

-- | Find the XtorSig belonging to a given XtorName.
lookupXtorSig :: EnvReader a m
              => Loc -> XtorName -> PolarityRep pol -> m (XtorSig pol)
lookupXtorSig loc xtn PosRep = do
  decl <- lookupDataDecl loc xtn
  case find ( \sig -> sig.sig_name == xtn ) (fst decl.data_xtors) of
    Just xts -> pure xts
    Nothing -> throwOtherError loc ["XtorName " <> xtn.unXtorName <> " not found in declaration of type " <> decl.data_name.rnTnName.unTypeName]
lookupXtorSig loc xtn NegRep = do
  decl <- lookupDataDecl loc xtn
  case find ( \sig -> sig.sig_name == xtn ) (snd decl.data_xtors) of
    Just xts -> pure xts
    Nothing -> throwOtherError loc ["XtorName " <> xtn.unXtorName <> " not found in declaration of type " <> decl.data_name.rnTnName.unTypeName]


lookupXtorSigUpper :: EnvReader a m
                   => Loc -> XtorName -> m (XtorSig Neg)
lookupXtorSigUpper loc xt = do
  decl <- lookupDataDecl loc xt
  case decl of
    NominalDecl { } -> do
      throwOtherError loc ["lookupXtorSigUpper: Expected refinement type but found nominal type."]
    decl@RefinementDecl {} -> do
      case find ( \sig -> sig.sig_name == xt ) (snd decl.data_xtors_refined) of
        Nothing -> throwOtherError loc ["lookupXtorSigUpper: Constructor/Destructor " <> ppPrint xt <> " not found"]
        Just sig -> pure sig



lookupXtorSigLower :: EnvReader a m
                   => Loc -> XtorName -> m (XtorSig Pos)
lookupXtorSigLower loc xt = do
  decl <- lookupDataDecl loc xt
  case decl of
    NominalDecl {} -> do
      throwOtherError loc ["lookupXtorSigLower: Expected refinement type but found nominal type."]
    decl@RefinementDecl {} -> do
      case find ( \sig -> sig.sig_name == xt ) (fst decl.data_xtors_refined) of
        Nothing ->  throwOtherError loc ["lookupXtorSigLower: Constructor/Destructor " <> ppPrint xt <> " not found"]
        Just sig -> pure sig



-- | Find the class declaration for a classname.
lookupClassDecl :: EnvReader a m
               => Loc -> ClassName -> m ClassDeclaration
lookupClassDecl loc cn = do
  let err = ErrOther $ SomeOtherError loc ("Undeclared class " <> ppPrint cn <> " is not contained in environment.")
  let f env = M.lookup cn env.classEnv
  snd <$> findFirstM f err

-- | Find the type of a method in a given class declaration.
lookupMethodType :: EnvReader a m
               => Loc -> MethodName -> ClassDeclaration -> PolarityRep pol -> m (LinearContext pol)
lookupMethodType loc mn decl PosRep =
  case find ( \sig -> sig.msig_name == mn) (fst decl.classdecl_methods) of
    Nothing -> throwOtherError loc ["Method " <> ppPrint mn <> " is not declared in class " <> ppPrint decl.classdecl_name]
    Just msig -> pure msig.msig_args
lookupMethodType loc mn decl NegRep =
  case find ( \sig-> sig.msig_name == mn) (snd decl.classdecl_methods) of
    Nothing -> throwOtherError loc ["Method " <> ppPrint mn <> " is not declared in class " <> ppPrint decl.classdecl_name]
    Just msig -> pure msig.msig_args

lookupXtorKind :: EnvReader a m
             => Loc -> XtorName -> m EvaluationOrder
lookupXtorKind loc xtorn = do
  let err = ErrOther $ SomeOtherError loc ("No Kinds for XTor " <> ppPrint xtorn)
  snd <$> findFirstM f err
  where 
    containsXtor :: XtorSig Pos -> Bool
    containsXtor sig = sig.sig_name == xtorn
    typeContainsXtor :: DataDecl -> Bool
    typeContainsXtor decl@NominalDecl {} | or (containsXtor <$> fst decl.data_xtors) = True
                                                      | otherwise = False
    typeContainsXtor decl@RefinementDecl {} | or (containsXtor <$> fst decl.data_xtors) = True
                                                      | otherwise = False

    f :: Environment -> Maybe EvaluationOrder
    f env = 
      case (find typeContainsXtor (fmap snd env.declEnv),M.lookup xtorn env.xtorEnv) of 
       (Just decl,_) -> Just (decl.data_kind.returnKind); 
       (_,Just xt) -> Just xt.strxtordecl_evalOrder; 
       (Nothing,Nothing) -> Nothing 



lookupStructuralXtor :: EnvReader a m
                => XtorName -> m RST.StructuralXtorDeclaration
lookupStructuralXtor xtorn = do 
  let err = ErrOther $ SomeOtherError defaultLoc ("Xtor " <> ppPrint xtorn <> " not found in program")
  let f env = M.lookup xtorn env.xtorEnv
  snd <$> findFirstM f err

---------------------------------------------------------------------------------
-- Run a computation in a locally changed environment.
---------------------------------------------------------------------------------

withTerm :: forall a m b pc. EnvReader a m
         => ModuleName -> PrdCnsRep pc -> FreeVarName -> Term pc -> Loc -> TypeScheme (PrdCnsToPol pc)
         -> (m b -> m b)
withTerm mn PrdRep fv tm loc tys action = do
  let modifyEnv :: Environment -> Environment
      modifyEnv env =
        env { prdEnv = M.insert fv (tm,loc,tys) env.prdEnv }
  let modifyEnvMap :: (Map ModuleName Environment, a) -> (Map ModuleName Environment, a)
      modifyEnvMap (map, rest) =
        case M.lookup mn map of
          Nothing -> (M.insert mn (modifyEnv emptyEnvironment) map, rest)
          Just _  -> (M.adjust modifyEnv mn map, rest)
  local modifyEnvMap action
withTerm mn CnsRep fv tm loc tys action = do
  let modifyEnv :: Environment -> Environment
      modifyEnv env =
        env { cnsEnv = M.insert fv (tm,loc,tys) env.cnsEnv }
  let modifyEnvMap :: (Map ModuleName Environment, a) -> (Map ModuleName Environment, a)
      modifyEnvMap (map, rest) =
        case M.lookup mn map of
          Nothing ->  (M.insert mn (modifyEnv emptyEnvironment) map, rest)
          Just _  -> (M.adjust modifyEnv mn map, rest)
  local modifyEnvMap action

