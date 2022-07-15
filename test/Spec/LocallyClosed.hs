module Spec.LocallyClosed where

import Control.Monad (forM_)
import Data.Text qualified as T
import Test.Hspec

import Pretty.Pretty ( ppPrintString )
import Pretty.Errors ()
import Syntax.TST.Terms ( Term, termLocallyClosed )
import Syntax.TST.Program qualified as TST
import Syntax.Common
import Errors ( Error )

type Reason = String

pendingFiles :: [(FilePath, Reason)]
pendingFiles = [ ("examples/TypeClasses.ds", "Backend not implemented for type classes")
               ]

getProducers :: TST.Program -> [(FreeVarName, Term Prd)]
getProducers prog = go prog []
  where
    go :: TST.Program -> [(FreeVarName, Term Prd)] -> [(FreeVarName, Term Prd)]
    go [] acc = acc
    go ((TST.PrdCnsDecl PrdRep (TST.MkPrdCnsDeclaration _ _ PrdRep _ fv _ tm)):rest) acc = go rest ((fv,tm):acc)
    go (_:rest) acc = go rest acc


spec :: [(FilePath, Either Error TST.Program)] -> Spec
spec examples = do
  describe "All examples are locally closed." $ do
    forM_ examples $ \(example, eitherEnv) -> do
      case example `lookup` pendingFiles of
        Just reason -> it "" $ pendingWith $ "Could check local closure of file " ++ example ++ "\nReason: " ++ reason
        Nothing     -> describe ("Examples in " ++ example ++ " are locally closed") $ do
          case eitherEnv of
            Left err -> it "Could not load examples." $ expectationFailure (ppPrintString err)
            Right env -> do
              forM_ (getProducers env) $ \(name,term) -> do
                it (T.unpack (unFreeVarName name) ++ " does not contain dangling deBruijn indizes") $
                  termLocallyClosed term `shouldBe` Right ()

