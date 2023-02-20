module Spec.LocallyClosed where

import Control.Monad (forM_, foldM)
import Data.Text qualified as T
import Data.List.NonEmpty (NonEmpty)
import Test.Hspec

import Pretty.Pretty ( ppPrintString )
import Pretty.Errors ()
import Syntax.Core.Terms (Pattern(..))
import Syntax.TST.Terms ( InstanceCase (instancecase_pat), Term, termLocallyClosed, instanceCaseLocallyClosed)
import Syntax.TST.Program qualified as TST
import Syntax.CST.Names
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
import Errors ( Error )
import Data.Either (isRight)
import Utils (moduleNameToFullPath)

type Reason = String

pendingFiles :: [(ModuleName, Reason)]
pendingFiles = [(  MkModuleName [] "ListRefinement" ,"Type Applications to Refinement Types aren't fully implemented yet"), (MkModuleName [] "Refinements", "Type Applications to Refinement Types aren't fully implemented yet")]

getProducers :: TST.Module -> [(FreeVarName, Term Prd)]
getProducers TST.MkModule { mod_decls } = go mod_decls []
  where
    go :: [TST.Declaration] -> [(FreeVarName, Term Prd)] -> [(FreeVarName, Term Prd)]
    go [] acc = acc
    go ((TST.PrdCnsDecl PrdRep (TST.MkPrdCnsDeclaration _ _ PrdRep _ fv _ tm)):rest) acc = go rest ((fv,tm):acc)
    go (_:rest) acc = go rest acc

getInstanceCases :: TST.Module -> [InstanceCase]
getInstanceCases TST.MkModule { mod_decls } = go mod_decls []
  where
    go :: [TST.Declaration] -> [InstanceCase] -> [InstanceCase]
    go [] acc = acc
    go ((TST.InstanceDecl (TST.MkInstanceDeclaration _ _ _ _ _ cases)):rest) acc = go rest (cases++acc)
    go (_:rest) acc = go rest acc


-- TODO: Wie kann ich alle Teiltests hier aufsammeln, und bei einem Fehlschlag einen Error zurückgeben, ohne den Rest der Tests abzubrechen?
spec :: Monad m => ((FilePath, ModuleName), Either (NonEmpty Error) TST.Module)
              -> m (((FilePath, ModuleName), Either (NonEmpty Error) TST.Module), Spec)
spec ((fp, mn), tst) = do
    let fullName = moduleNameToFullPath mn fp
    case mn `lookup` pendingFiles of
      Just reason -> return (((fp, mn), tst),
                            it "" $ pendingWith $ "Could check local closure of file " ++ fullName ++ "\nReason: " ++ reason)
      Nothing     -> do
        let pendingDescribe = describe ("Examples in " ++ fullName ++ " are locally closed")
        case tst of
          Left err -> return (((fp, mn), tst),
                              it "Could not load examples." $ expectationFailure (ppPrintString err))
          Right env -> do
            -- fold producer and instance checks for deBrujin indizes:
            danglingProducers <- foldM foldProducers (Nothing, return()) (getProducers env)
            danglingInstanceClasses <- foldM foldInstanceClasses (Nothing, return()) (getInstanceCases env)
            let returnSpec = pendingDescribe (snd danglingProducers >> snd danglingInstanceClasses)
            let returnErrorCase = case (fst danglingProducers, fst danglingInstanceClasses) of
                                          (Just (Left err), _) -> Left (pure err)
                                          (_, Just (Left err)) -> Left (pure err)
                                          (_, _)        -> tst
            return (((fp, mn), returnErrorCase), returnSpec)

            where foldProducers (failure, specSequence) (name, term) = do
                                        let locallyClosed = termLocallyClosed term
                                        let msg = it (T.unpack (unFreeVarName name) ++ " does not contain dangling deBruijn indizes")
                                        let danglingSpec = msg $ locallyClosed `shouldSatisfy` isRight
                                        let fail = case locallyClosed of
                                                        Left err -> Just locallyClosed
                                                        Right _  -> Nothing 
                                        return (fail,
                                                danglingSpec >> specSequence)
                  foldInstanceClasses (failure, specSequence) instance_case = do
                                        let locallyClosed = instanceCaseLocallyClosed instance_case
                                        let msg = it (T.unpack (unXtorName $ (\(XtorPat _ xt _) -> xt) $ instancecase_pat instance_case) ++ " does not contain dangling deBruijn indizes")
                                        let danglingSpec = msg $ locallyClosed `shouldSatisfy` isRight
                                        let fail = case locallyClosed of
                                                        Left err -> Just locallyClosed
                                                        Right _  -> Nothing 
                                        return (fail,
                                                danglingSpec >> specSequence)



