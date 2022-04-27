module Spec.LocallyClosed where

import Control.Monad (forM_)
import Data.Text qualified as T
import Test.Hspec

import Pretty.Pretty ( ppPrintString )
import Pretty.Errors ()
import Syntax.AST.Terms ( Term, termLocallyClosed )
import Syntax.AST.Program qualified as AST
import Syntax.Common
import Errors ( Error )

getProducers :: AST.Program -> [(FreeVarName, Term Prd)]
getProducers prog = go prog []
  where
    go :: AST.Program -> [(FreeVarName, Term Prd)] -> [(FreeVarName, Term Prd)]
    go [] acc = acc
    go ((AST.PrdCnsDecl _ _ PrdRep _ fv _ tm):rest) acc = go rest ((fv,tm):acc)
    go (_:rest) acc = go rest acc


spec :: [(FilePath, Either Error AST.Program)] -> Spec
spec examples = do
  describe "All examples are locally closed." $ do
    forM_ examples $ \(example, eitherEnv) -> do
      describe ("Examples in " ++ example ++ " are locally closed") $ do
        case eitherEnv of
          Left err -> it "Could not load examples." $ expectationFailure (ppPrintString err)
          Right env -> do
            forM_ (getProducers env) $ \(name,term) -> do
              it (T.unpack (unFreeVarName name) ++ " does not contain dangling deBruijn indizes") $
                termLocallyClosed term `shouldBe` Right ()

