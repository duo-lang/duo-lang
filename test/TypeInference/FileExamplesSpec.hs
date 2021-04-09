module TypeInference.FileExamplesSpec ( spec ) where

import           Test.Hspec
import           Control.Monad (forM_)

import qualified Data.Map as M
import Data.Either (isRight)

import TestUtils
import Pretty.Pretty
import Pretty.Errors ()
import Syntax.STerms
import Syntax.Types
import Syntax.Program
import TypeInference.InferTypes
import Utils

instance Show (TypeScheme pol) where
  show = ppPrint

checkTerm :: PrdCnsRep pc -> Environment FreeVarName -> (FreeVarName, STerm pc Loc FreeVarName) -> SpecWith ()
checkTerm rep env (name,term) = it (name ++ " can be typechecked correctly") $
  inferSTerm rep term env `shouldSatisfy` isRight

checkCommand :: Environment FreeVarName -> (FreeVarName, Command Loc FreeVarName) -> SpecWith ()
checkCommand env (name,cmd) = it (name ++ " can be typechecked") $
  checkCmd cmd env `shouldSatisfy` isRight

-- | Typecheck the programs in the toplevel "examples/" subfolder.
spec :: Spec
spec = do
  describe "All the programs in the toplevel \"examples/\" folder typecheck." $ do
    examples <- runIO getAvailableExamples
    forM_ examples $ \example -> do
      describe ("The file " ++ example ++ " typechecks.") $ do
        env <- runIO $ getEnvironment example
        case env of
          Left err -> it "Could not load examples" $ expectationFailure (ppPrint err)
          Right env -> return ()
