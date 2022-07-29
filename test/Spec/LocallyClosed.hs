module Spec.LocallyClosed where

import Control.Monad (forM_)
import Data.Text qualified as T
import Data.List.NonEmpty (NonEmpty)
import Test.Hspec

import Pretty.Pretty ( ppPrintString )
import Pretty.Errors ()
import Syntax.TST.Terms ( InstanceCase (instancecase_pat), Term, termLocallyClosed, instanceCaseLocallyClosed, Pattern (XtorPat) )
import Syntax.TST.Program qualified as TST
import Syntax.Common
import Errors ( Error )
import Data.Either (isRight)

type Reason = String

pendingFiles :: [(FilePath, Reason)]
pendingFiles = []

getProducers :: TST.Program -> [(FreeVarName, Term Prd)]
getProducers prog = go prog []
  where
    go :: TST.Program -> [(FreeVarName, Term Prd)] -> [(FreeVarName, Term Prd)]
    go [] acc = acc
    go ((TST.PrdCnsDecl PrdRep (TST.MkPrdCnsDeclaration _ _ PrdRep _ fv _ tm)):rest) acc = go rest ((fv,tm):acc)
    go (_:rest) acc = go rest acc

getInstanceCases :: TST.Program -> [InstanceCase]
getInstanceCases prog = go prog []
  where
    go :: TST.Program -> [InstanceCase] -> [InstanceCase]
    go [] acc = acc
    go ((TST.InstanceDecl (TST.MkInstanceDeclaration _ _ _ _ cases)):rest) acc = go rest (cases++acc)
    go (_:rest) acc = go rest acc

spec :: [(FilePath, Either (NonEmpty Error) TST.Program)] -> Spec
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
                  termLocallyClosed term `shouldSatisfy` isRight
              forM_ (getInstanceCases env) $ \instance_case -> do
                it (T.unpack (unXtorName $ (\(XtorPat _ xt _) -> xt) $ instancecase_pat instance_case) ++ " does not contain dangling deBruijn indizes") $
                  instanceCaseLocallyClosed instance_case `shouldSatisfy` isRight

