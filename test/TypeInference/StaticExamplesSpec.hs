module TypeInference.StaticExamplesSpec ( spec )  where

import Control.Monad (forM_)
import Data.Text (Text)
import qualified Data.Text as T
import System.FilePath
import Test.Hspec

import TestUtils
import Parser.Parser
import Pretty.Pretty
import Pretty.Errors ()
import Syntax.STerms
import Syntax.Types
import Syntax.Program
import TypeInference.InferProgram
import TypeInference.GenerateConstraints.Definition (InferenceMode(..))
import TypeAutomata.ToAutomaton
import TypeAutomata.Subsume (typeAutEqual)
import Utils

instance Show (TypeScheme pol) where
  show = ppPrintString

typecheckExample :: Environment FreeVarName -> Text -> Text -> Spec
typecheckExample env termS typS = do
  it (T.unpack termS ++  " typechecks as: " ++ T.unpack typS) $ do
      let Right (term,loc) = runInteractiveParser (stermP PrdRep) termS
      let Right inferredTypeAut = trace_minTypeAut <$> inferSTermTraced NonRecursive (Loc loc loc) "" InferNominal PrdRep term env
      let Right specTypeScheme = runInteractiveParser (typeSchemeP PosRep) typS
      let Right specTypeAut = typeToAut specTypeScheme
      (inferredTypeAut `typeAutEqual` specTypeAut) `shouldBe` True

prgExamples :: [(Text,Text)]
prgExamples = 
    [ ( "\\(x)[k] => x >> k"
        , "forall a. { 'Ap(a)[a] }" )
    , ( "'S('Z)"
        , "< 'S(< 'Z >) >" )
    , ( "\\(b,x,y)[k] => b >> match { 'True => x >> k, 'False => y >> k }"
        , "forall a. { 'Ap(< 'True | 'False >, a, a)[a] }" )
    , ( "\\(b,x,y)[k] => b >> match { 'True => x >> k, 'False => y >> k }"
        , "forall a b. { 'Ap(<'True|'False>, a, b)[a \\/ b] }" )
    , ( "\\(f)[k] => (\\(x)[k] => f >> 'Ap(x)[mu y. f >> 'Ap(y)[k]]) >> k"
        , "forall a b. { 'Ap({ 'Ap(a \\/ b)[b] })[{ 'Ap(a)[b] }] }" )

    -- Nominal Examples
    , ( "\\(x)[k] => x >> match { TT => FF >> k, FF => TT >> k }"
        , "{ 'Ap(Bool)[Bool] }" )
    , ( "\\(x)[k] => x >> match { TT => FF >> k, FF => Z >> k }"
        , "{ 'Ap(Bool)[(Bool \\/ Nat)] }" )
    , ( "\\(x)[k] => x >> match { TT => FF >> k, FF => Z >> k }"
        , "{ 'Ap(Bool)[(Nat \\/ Bool)] }" )

    -- addNominal
    , ( "comatch { 'Ap(n,m)[k] => fix >> 'Ap( comatch { 'Ap(alpha)[k] => comatch { 'Ap(m)[k] => m >> match { Z => n >> k, S(p) => alpha >> 'Ap(p)[mu w. S(w) >> k] }} >> k })['Ap(m)[k]] }"
        , "{ 'Ap(Nat,Nat)[Nat] }" )

    -- mltNominal
    , ( "comatch { 'Ap(n,m)[k] => fix >> 'Ap(comatch { 'Ap(alpha)[k] => comatch { 'Ap(m)[k] => m >> match { Z => Z >> k, S(p) => alpha >> 'Ap(p)[mu w. addNominal >> 'Ap(n,w)[k]] } } >> k })['Ap(m)[k]]}"
        , "forall t0. { 'Ap((t0 /\\ Nat),Nat)[(t0 \\/ Nat)] }" )

    -- expNominal
    , ( "comatch { 'Ap(n,m)[k] => fix >> 'Ap(comatch { 'Ap(alpha)[k] => comatch { 'Ap(m)[k] => m >> match { Z => S(Z) >> k, S(p) => alpha >> 'Ap(p)[mu w. mltNominal >> 'Ap(n,w)[k]] } } >> k })['Ap(m)[k]] }"
        , "forall t0. { 'Ap((t0 /\\ Nat),Nat)[(t0 \\/ Nat)] }" )

    -- subSafeNominal
    , ( "comatch { 'Ap(n,m)[k] => fix >> 'Ap(comatch { 'Ap(alpha)[k] => comatch { 'Ap(n)[k] => comatch { 'Ap(m)[k] => m >> match { Z => n >> k, S(mp) => n >> match { Z => n >> k, S(np) => alpha >> 'Ap(np)['Ap(mp)[k]] }}} >> k } >> k })['Ap(n)['Ap(m)[k]]]}"
        , "forall t0. { 'Ap((t0 /\\ Nat),Nat)[(t0 \\/ Nat)] }" )

    ]

testFiles :: [FilePath]
testFiles = ["prg.ds", "prg_old.ds"]

typecheckInFile :: FilePath -> Spec
typecheckInFile fp =
  describe "Typecheck specific examples" $ do
    describe ("Context is " <> fp) $ do
        env <- runIO $ getEnvironment ("examples" </> fp) InferNominal
        case env of
            Left err -> it "Could not load environment" $ expectationFailure (ppPrintString err)
            Right env' -> do
                forM_ prgExamples $ uncurry $ typecheckExample env'

spec :: Spec
spec = forM_ testFiles typecheckInFile
