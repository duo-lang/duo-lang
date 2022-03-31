module Parser.ParserSpec ( spec ) where

import Test.Hspec
import Data.Text (Text)
import Data.Text qualified as T


import Driver.Definition
import Driver.Environment
import Parser.Parser
import Parser.Types (typP)
import Pretty.Errors ()
import Pretty.Terms ()
import Pretty.Types ()
import Renamer.Types
import Syntax.AST.Types
import Syntax.AST.Types qualified as AST
import Syntax.Common
import TestUtils (getEnvironment)

ds :: Environment Inferred ->  DriverState
ds env = DriverState defaultInferenceOptions { infOptsLibPath = ["examples"] } env

parseType :: Environment Inferred -> PolarityRep pol -> Text -> AST.Typ pol -> Spec
parseType env pol input expected = do
  it ("Parsing of " ++ T.unpack input ++ " works") $ do
    let parseResult = runInteractiveParser (fst <$> typP) input
    case parseResult of
      Left _err -> expectationFailure "Could not parse example type"
      Right result -> do
        lowerResult <- execDriverM (ds env) (lowerTyp pol result)
        case lowerResult of
          Left _err -> expectationFailure "Could not lower type"
          Right (result,_) -> case pol of -- Necessary to provide Show instance for (Typ pol)
            PosRep -> result `shouldBe` expected
            NegRep -> result `shouldBe` expected

parseTypeIdentical :: Environment Inferred -> PolarityRep pol -> Text -> Text -> Spec
parseTypeIdentical env pol input1 input2 =
  it ("Parsing of " ++ T.unpack input1 ++ " yields the same result as parsing " ++ T.unpack input2) $ do
    let parseResult1 = runInteractiveParser (fst <$> typP) input1
    let parseResult2 = runInteractiveParser (fst <$> typP) input2
    case (parseResult1, parseResult2) of
      (Left _err, _) -> expectationFailure "Could not parse left example"
      (_, Left _err) -> expectationFailure "Could not parse right example"
      (Right r1, Right r2) -> do
        lowerResult1 <- execDriverM (ds env) (lowerTyp pol r1)
        lowerResult2 <- execDriverM (ds env) (lowerTyp pol r2)
        case (lowerResult1, lowerResult2) of
          (Left _err, _) -> expectationFailure "Could not lower left example"
          (_, Left _err) -> expectationFailure "Could not lower right example"
          (Right (r1,_), Right (r2,_)) -> case pol of -- Necessary to provide Show instance for (Typ pol)
            PosRep -> r1 `shouldBe` r2
            NegRep -> r1 `shouldBe` r2

parseTypeSchemeIdentical :: Environment Inferred -> PolarityRep pol -> Text -> Text -> Spec
parseTypeSchemeIdentical env pol input1 input2 = do
  it ("Parsing of " ++ T.unpack input1 ++ " yields the same result as parsing " ++ T.unpack input2) $ do
    let parseResult1 = runInteractiveParser typeSchemeP input1
    let parseResult2 = runInteractiveParser typeSchemeP input2
    case (parseResult1, parseResult2) of
      (Left _err, _) -> expectationFailure "Could not parse left example"
      (_, Left _err) -> expectationFailure "Could not parse right example"
      (Right r1, Right r2) -> do
        lowerResult1 <- execDriverM (ds env) (lowerTypeScheme pol r1)
        lowerResult2 <- execDriverM (ds env) (lowerTypeScheme pol r2)
        case (lowerResult1, lowerResult2) of
          (Left _err, _) -> expectationFailure "Could not lower left example"
          (_, Left _err) -> expectationFailure "Could not lower right example"
          (Right (r1,_), Right (r2,_)) -> case pol of -- Necessary to provide Show instance for (TypScheme pol)
            PosRep -> r1 `shouldBe` r2
            NegRep -> r1 `shouldBe` r2


mkFun :: PolarityRep pol -> Typ (FlipPol pol) -> Typ pol -> Typ pol
mkFun rep t1 t2 = (TyNominal rep Nothing (MkTypeName "Fun") [t1] [t2])

mkNat :: PolarityRep pol -> Typ pol
mkNat rep = TyNominal rep Nothing (MkTypeName "Nat") [] []

spec :: Spec
spec = do
  describe "Check type parsing" $ do
    eenv <- runIO $ getEnvironment "examples/Peano.ds" defaultInferenceOptions { infOptsLibPath = ["examples"] }
    let env = case eenv of
                Left _ -> error "Could not load Peano.ds"
                Right env -> env
    parseType env PosRep
                 "< Nat | >"
                 (TyData PosRep (Just $ MkTypeName "Nat") [])
    parseType env PosRep
                 "{ A() }"
                 (TyCodata PosRep Nothing [MkXtorSig (MkXtorName "A") []])
    parseType env PosRep
                 "{ A[{ B }] }"
                 (TyCodata PosRep Nothing [MkXtorSig (MkXtorName "A") [PrdCnsType CnsRep $ TyCodata PosRep Nothing [MkXtorSig (MkXtorName "B") []] ]])
    parseType env PosRep
                 "{ Fun | }"
                 (TyCodata PosRep (Just $ MkTypeName "Fun") [])
    parseType env PosRep
                 "< X(< Nat | >) >"
                 (TyData PosRep Nothing [MkXtorSig (MkXtorName "X") [ PrdCnsType PrdRep $ TyData PosRep (Just $ MkTypeName "Nat") [] ]])
    parseType env PosRep
                 "< Nat | S >"
                 (TyData PosRep (Just $ MkTypeName "Nat") [MkXtorSig (MkXtorName "S") []])
    parseType env PosRep
                 "{ Foo |  A[{ B }]  }"
                 (TyCodata PosRep (Just $ MkTypeName "Foo")
                           [MkXtorSig (MkXtorName "A") [PrdCnsType CnsRep $ TyCodata PosRep Nothing [MkXtorSig (MkXtorName "B") []] ]])
    parseType env NegRep
                 "< A , B > /\\ < B >"
                 (TySet NegRep Nothing [ TyData   NegRep Nothing [MkXtorSig (MkXtorName "A") mempty, MkXtorSig (MkXtorName "B") mempty]
                                       , TyData   NegRep Nothing [MkXtorSig (MkXtorName "B") mempty]])
    parseType env PosRep
                 "< A , B > \\/ < B >"
                 (TySet PosRep Nothing [ TyData   PosRep Nothing [MkXtorSig (MkXtorName "A") mempty, MkXtorSig (MkXtorName "B") mempty]
                                       , TyData   PosRep Nothing [MkXtorSig (MkXtorName "B") mempty]])
    parseType env NegRep
                 "{ A , B } /\\ { B }"
                 (TySet NegRep Nothing [ TyCodata NegRep Nothing [MkXtorSig (MkXtorName "A") mempty, MkXtorSig (MkXtorName "B") mempty]
                                       , TyCodata NegRep Nothing [MkXtorSig (MkXtorName "B") mempty]])
    parseType env PosRep
                 "{ A , B} \\/ { B }"
                 (TySet PosRep Nothing [ TyCodata PosRep Nothing [MkXtorSig (MkXtorName "A") mempty, MkXtorSig (MkXtorName "B") mempty]
                                       , TyCodata PosRep Nothing [MkXtorSig (MkXtorName "B") mempty]])
    parseType env PosRep
                 "Nat -> Nat"
                 (mkFun PosRep (mkNat NegRep) (mkNat PosRep))
    parseType env NegRep
                 "Nat -> Nat"
                 (mkFun NegRep (mkNat PosRep) (mkNat NegRep))
    parseType env PosRep
                 "Nat -> Nat -> Nat"
                 (mkFun PosRep (mkNat NegRep) (mkFun PosRep (mkNat NegRep) (mkNat PosRep)))
    parseType env NegRep
                 "Nat -> Nat -> Nat"
                 (mkFun NegRep (mkNat PosRep) (mkFun NegRep (mkNat PosRep) (mkNat NegRep)))

    parseTypeIdentical env PosRep "Nat -> Nat -> Nat" "Nat -> (Nat -> Nat)"
    parseTypeIdentical env NegRep "Nat -> Nat -> Nat" "Nat -> (Nat -> Nat)"

    parseTypeSchemeIdentical env PosRep "forall a b c d e f. a /\\ b -> c /\\ d -> e \\/ f" "forall a b c d e f. (a /\\ b) -> ((c /\\ d) -> (e \\/ f))"
    parseTypeSchemeIdentical env NegRep "forall a b c d e f. a \\/ b -> c \\/ d -> e /\\ f" "forall a b c d e f. (a \\/ b) -> ((c \\/ d) -> (e /\\ f))"
    parseTypeSchemeIdentical env PosRep "forall a b c. a \\/ b \\/ c" "forall a b c. (a \\/ b) \\/ c"
    parseTypeSchemeIdentical env NegRep "forall a b c. a /\\ b /\\ c" "forall a b c. (a /\\ b) /\\ c"
