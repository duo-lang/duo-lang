module Spec.LocallyClosed where

import Control.Monad (forM_)
import Data.Map qualified as M
import Data.Text qualified as T
import Test.Hspec

import Driver.Environment
import Pretty.Pretty
import Pretty.Errors ()
import Syntax.AST.Terms
import Syntax.Common
import Errors

spec :: [(FilePath, Either Error Environment)] -> Spec
spec examples = do
  describe "All examples are locally closed." $ do
    forM_ examples $ \(example, eitherEnv) -> do
      describe ("Examples in " ++ example ++ " are locally closed") $ do
        case eitherEnv of
          Left err -> it "Could not load examples." $ expectationFailure (ppPrintString err)
          Right env -> do
            forM_ (M.toList (prdEnv env)) $ \(name,(term,_,_)) -> do
              it (T.unpack (unFreeVarName name) ++ " does not contain dangling deBruijn indizes") $
                termLocallyClosed term `shouldBe` Right ()

