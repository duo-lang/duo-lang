module Renamer.Definition where

import Control.Monad.Except (MonadError, Except, throwError, runExcept)
import Control.Monad.Reader
import Data.Bifunctor (second)
import Data.Map qualified as M
import Data.List (find)

import Pretty.Pretty
import Pretty.Common ()
import Pretty.Types ()
import Renamer.SymbolTable
import Syntax.Common
import Utils
import Errors

------------------------------------------------------------------------------
-- Renamer Monad
------------------------------------------------------------------------------

type RenameReader = [(ModuleName, SymbolTable)]

newtype RenamerM a = MkRenamerM { unRenamerM :: ReaderT RenameReader (Except Error) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadReader RenameReader)

runRenamerM :: RenameReader -> RenamerM a -> Either Error a
runRenamerM reader action = runExcept (runReaderT (unRenamerM action) reader)

------------------------------------------------------------------------------
-- Helper Functions
------------------------------------------------------------------------------

getSymbolTables :: RenamerM [(ModuleName, SymbolTable)]
getSymbolTables = ask

-- | Returns the first "(a,Just b)" result in the list.
firstResult :: [(a, Maybe b)] -> Maybe (a,b)
firstResult [] = Nothing
firstResult ((x,Just y):_) = Just (x,y)
firstResult ((_,Nothing):rest) = firstResult rest

lookupXtor :: Loc
           -- ^ The location of the xtor to be looked up
           -> (XtorName, DataCodata)
           -- ^ The name of the xtor and whether we expect a ctor or dtor
           -> RenamerM (ModuleName, (NominalStructural, Arity))
           -- ^ The module where the xtor comes from, its sort and arity.
lookupXtor loc xs@(xtor,dc) = do
  symbolTables <- getSymbolTables
  let results :: [(ModuleName, Maybe (NominalStructural, Arity))]
      results = second (\st -> M.lookup xs (xtorMap st)) <$> symbolTables
  case firstResult results of
    Just res -> pure res
    Nothing -> throwError $ OtherError (Just loc) ((case dc of Data -> "Constructor"; Codata -> "Destructor") <>" not in symbol table: " <> ppPrint xtor)
    

-- | Find the Arity of a given typename
lookupTypeConstructor :: Loc
                      -- ^ The location of the typename to be looked up
                      -> TypeName
                      -- ^ The typename to look up
                      -> RenamerM (ModuleName, TyConResult)
                      -- ^ The module where the typename is introduced, and the relevant info.
lookupTypeConstructor loc tn = do
    symbolTables <- getSymbolTables
    let results :: [(ModuleName, Maybe TyConResult)]
        results = second (\st -> M.lookup tn (tyConMap st)) <$> symbolTables
    case firstResult results of
        Just res -> pure res
        Nothing -> throwError (OtherError (Just loc) ("Type name " <> unTypeName tn <> " not found in symbol table"))

lookupTyOp :: Loc
           -> BinOp
           -> RenamerM (ModuleName, TyOp)
lookupTyOp loc op = do
  symbolTables <- getSymbolTables
  let results :: [(ModuleName, Maybe TyOp)]
      results = second (\st -> find (\tyop -> symbol tyop == op) (tyOps st)) <$> symbolTables
  case firstResult results of
    Just res -> pure res
    Nothing -> throwError (LowerError (Just loc) (UnknownOperator (ppPrint op)))
      