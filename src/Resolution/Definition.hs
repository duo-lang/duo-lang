module Resolution.Definition where

import Control.Monad.Except (MonadError, Except, throwError, runExcept)
import Control.Monad.Reader
import Data.Bifunctor (second)
import Data.Map (Map)
import Data.Map qualified as M
import Data.List (find)
import Data.Text qualified as T

import Pretty.Pretty
import Pretty.Common ()
import Pretty.Types ()
import Resolution.SymbolTable
import Syntax.Common
import Utils
import Errors

------------------------------------------------------------------------------
-- Resolver Monad
------------------------------------------------------------------------------

type ResolveReader = Map ModuleName SymbolTable

newtype ResolverM a = MkResolverM { unResolverM :: ReaderT ResolveReader (Except Error) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadReader ResolveReader)

instance MonadFail ResolverM where
  fail str = throwError (OtherError Nothing (T.pack str))

runResolverM :: ResolveReader -> ResolverM a -> Either Error a
runResolverM reader action = runExcept (runReaderT (unResolverM action) reader)

------------------------------------------------------------------------------
-- Helper Functions
------------------------------------------------------------------------------

filterJusts :: [(a, Maybe b)] -> [(a,b)]
filterJusts [] = []
filterJusts ((_,Nothing):xs) = filterJusts xs
filterJusts ((x,Just y):xs) = (x,y):(filterJusts xs)

lookupXtor :: Loc
           -- ^ The location of the xtor to be looked up
           -> XtorName
           -- ^ The name of the xtor and whether we expect a ctor or dtor
           -> ResolverM (ModuleName, XtorNameResolve)
           -- ^ The module where the xtor comes from, its sort and arity.
lookupXtor loc xtor = do
  symbolTables <- M.toList <$> ask
  let results :: [(ModuleName, Maybe XtorNameResolve)]
      results = second (\st -> M.lookup xtor (xtorNameMap st)) <$> symbolTables
  case filterJusts results of
    []    -> throwError $ OtherError (Just loc) ("Constructor/Destructor not in symbol table: " <> ppPrint xtor)
    [res] -> pure res
    _     -> throwError $ OtherError (Just loc) ("Constructor/Destructor found in multiple modules: " <> ppPrint xtor)
    

-- | Find the Arity of a given typename
lookupTypeConstructor :: Loc
                      -- ^ The location of the typename to be looked up
                      -> TypeName
                      -- ^ The typename to look up
                      -> ResolverM TypeNameResolve
                      -- ^ The resolved typename, and the relevant info.
lookupTypeConstructor loc tn = do
    symbolTables <- M.toList <$> ask
    let results :: [(ModuleName, Maybe TypeNameResolve)]
        results = second (\st -> M.lookup tn (typeNameMap st)) <$> symbolTables
    case filterJusts results of
      []         -> throwError (OtherError (Just loc) ("Type name " <> unTypeName tn <> " not found in symbol table."))
      [(_,res)]  -> pure res
      xs         -> throwError (OtherError (Just loc) ("Type name " <> unTypeName tn <> " found in multiple imports.\nModules: " <> T.pack (show(fst <$> xs))))

-- | Type operator for the union type
unionTyOp :: TyOp
unionTyOp = MkTyOp
  { symbol = UnionOp
  , prec = MkPrecedence 1
  , assoc = LeftAssoc
  , desugar = UnionDesugaring
  }

-- | Type operator for the intersection type
interTyOp :: TyOp
interTyOp = MkTyOp
  { symbol = InterOp
  , prec = MkPrecedence 2
  , assoc = LeftAssoc
  , desugar = InterDesugaring
  }

lookupTyOp :: Loc
           -> BinOp
           -> ResolverM (ModuleName, TyOp)
lookupTyOp _ UnionOp = pure (MkModuleName "<BUILTIN>", unionTyOp)
lookupTyOp _ InterOp = pure (MkModuleName "<BUILTIN>", interTyOp)
lookupTyOp loc op = do
  symbolTables <- M.toList <$> ask
  let results :: [(ModuleName, Maybe TyOp)]
      results = second (\st -> find (\tyop -> symbol tyop == op) (tyOps st)) <$> symbolTables
  case filterJusts results of
    []    -> throwError (LowerError (Just loc) (UnknownOperator (ppPrint op)))
    [res] -> pure res
    _     -> throwError (OtherError (Just loc) ("Type operator " <> ppPrint op <> " found in multiple imports."))
      