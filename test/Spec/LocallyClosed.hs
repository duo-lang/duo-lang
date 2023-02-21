module Spec.LocallyClosed where

import Control.Monad (foldM)
import Data.Text qualified as T
import Test.Hspec
import Pretty.Errors ()
import Syntax.Core.Terms (Pattern(..))
import Syntax.TST.Terms ( InstanceCase (instancecase_pat), Term, termLocallyClosed, instanceCaseLocallyClosed)
import Syntax.TST.Program qualified as TST
import Syntax.CST.Names
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
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
spec :: Monad m => ((FilePath, ModuleName), TST.Module)
              -> m (Maybe ((FilePath, ModuleName), TST.Module), Spec)
spec ((fp, mn), env) = do
    let fullName = moduleNameToFullPath mn fp
    case mn `lookup` pendingFiles of
      Just reason -> return (Nothing,
                            it "" $ pendingWith $ "Could check local closure of file " ++ fullName ++ "\nReason: " ++ reason)
      Nothing     -> do
        let pendingDescribe = describe ("Examples in " ++ fullName ++ " are locally closed")
        -- fold producer and instance checks for deBrujin indizes:
        danglingProducers <- foldM foldProducers (Nothing, return()) (getProducers env)
        danglingInstanceClasses <- foldM foldInstanceClasses (Nothing, return()) (getInstanceCases env)
        let returnSpec = pendingDescribe (snd danglingProducers >> snd danglingInstanceClasses)
        case (fst danglingProducers, fst danglingInstanceClasses) of
                (Nothing, Nothing) -> return (Just ((fp, mn), env), returnSpec)
                _                  -> return (Nothing, returnSpec)

        where foldProducers (failure, specSequence) (name, term) = do
                                    let locallyClosed = termLocallyClosed term
                                    let msg = it (T.unpack (unFreeVarName name) ++ " does not contain dangling deBruijn indizes")
                                    let danglingSpec = msg $ locallyClosed `shouldSatisfy` isRight
                                    let fail = case failure of
                                                    Nothing -> if isRight locallyClosed then Nothing else Just locallyClosed
                                                    x       -> x
                                    return (fail,
                                            danglingSpec >> specSequence)
              foldInstanceClasses (failure, specSequence) instance_case = do
                                    let locallyClosed = instanceCaseLocallyClosed instance_case
                                    let msg = it (T.unpack (unXtorName $ (\(XtorPat _ xt _) -> xt) $ instancecase_pat instance_case) ++ " does not contain dangling deBruijn indizes")
                                    let danglingSpec = msg $ locallyClosed `shouldSatisfy` isRight
                                    let fail = case failure of
                                                    Nothing -> if isRight locallyClosed then Nothing else Just locallyClosed
                                                    x       -> x 
                                    return (fail,
                                            danglingSpec >> specSequence)



