module LSP.Handler.Hover ( hoverHandler ) where

import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.IORef (readIORef)
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Text (Text)
import Data.Map (Map)
import Data.List.NonEmpty qualified as NE
import Language.LSP.Types
import Language.LSP.Server
    ( requestHandler, Handlers, getConfig )
import LSP.Definition ( LSPMonad, LSPConfig (MkLSPConfig), sendInfo )
import LSP.MegaparsecToLSP ( locToRange, lookupInRangeMap )
import System.Log.Logger ( debugM )

import Pretty.Pretty ( ppPrint )
import Pretty.Common ()
import Pretty.Types ()
import Pretty.Terms ()
import Syntax.CST.Names
    ( MethodName, ClassName)
import Syntax.RST.Names
import Syntax.CST.Kinds ( MonoKind )
import Syntax.RST.Kinds ( AnyKind )
import Syntax.CST.Types ( PrdCnsRep(..), DataCodata(..), PrdCns(..))
import Syntax.TST.Terms
    ( Command(Method, Print, Read, Jump, ExitSuccess, ExitFailure,
              PrimOp),
      Term(PrimLitString, BoundVar, FreeVar, PrimLitI64, PrimLitF64,
           PrimLitChar),
      InstanceCase(instancecase_cmd),
      CmdCase(cmdcase_cmd),
      Substitution(unSubstitution),
      PrdCnsTerm(..) )
import Syntax.TST.Terms qualified as TST
import Syntax.TST.Program qualified as TST
import Sugar.TST
import Syntax.TST.Types qualified as TST
import Syntax.RST.Types (PolarityRep(..))
import Loc (Loc)
import Syntax.RST.Program qualified as RST
import Syntax.RST.Terms qualified as RST
import Syntax.CST.Program qualified as CST
import Syntax.RST.Program (StructuralXtorDeclaration(strxtordecl_evalOrder))

---------------------------------------------------------------------------------
-- Handle Type on Hover
---------------------------------------------------------------------------------

type HoverMap   = Map Range Hover

hoverHandler :: Handlers LSPMonad
hoverHandler = requestHandler STextDocumentHover $ \req responder ->  do
  let (RequestMessage _ _ _ (HoverParams (TextDocumentIdentifier uri) pos _)) = req
  liftIO $ debugM "lspserver.hoverHandler" ("Received hover request: " <> show uri <> " at: " <> show pos)
  MkLSPConfig ref <- getConfig
  cache <- liftIO $ readIORef ref
  case M.lookup uri cache of
    Nothing -> do
      sendInfo ("Cache not initialized for: " <> T.pack (show uri))
      responder (Right Nothing)
    Just mod -> responder (Right (lookupInRangeMap pos (toHoverMap mod)))

---------------------------------------------------------------------------------
-- Generating HoverMaps
---------------------------------------------------------------------------------

-- | A class for generating HoverMaps
class ToHoverMap a where
  toHoverMap :: a -> HoverMap

mkHover :: Text -> Range ->  Hover
mkHover txt rng = Hover (HoverContents (MarkupContent MkMarkdown txt)) (Just rng)

mkHoverMap :: Loc -> Text -> HoverMap
mkHoverMap loc msg = M.fromList [(locToRange loc, mkHover msg (locToRange loc))]

---------------------------------------------------------------------------------
-- Converting Terms to a HoverMap
---------------------------------------------------------------------------------

instance ToHoverMap (TermCase pc) where
  toHoverMap tmcase = toHoverMap tmcase.tmcase_term

instance ToHoverMap (TermCaseI pc) where
  toHoverMap icase = toHoverMap icase.tmcasei_term

instance ToHoverMap CmdCase where
  toHoverMap cmdcase = toHoverMap cmdcase.cmdcase_cmd

instance ToHoverMap InstanceCase where
  toHoverMap icase = toHoverMap icase.instancecase_cmd


boundVarToHoverMap :: Loc -> TST.Typ pol -> HoverMap
boundVarToHoverMap loc ty = mkHoverMap loc msg
  where
    msg :: Text
    msg = T.unlines [ "#### Bound variable"
                    , "- Type : `" <> ppPrint ty <> "`"
                    ]

freeVarToHoverMap :: Loc -> TST.Typ pol -> HoverMap
freeVarToHoverMap loc ty = mkHoverMap loc msg 
  where
    msg :: Text
    msg = T.unlines [ "### Free Variable"
                    , "- Type `" <> ppPrint ty <> "`"
                    ]

xtorToHoverMap :: Loc -> PrdCnsRep pc -> TST.Typ pol -> RST.NominalStructural -> HoverMap
xtorToHoverMap loc pc ty ns =  mkHoverMap loc msg
  where
    msg :: Text
    msg = case pc of
      PrdRep -> T.unlines [ "#### " <> ppPrint ns <> " constructor"
                          , "- **Right-Intro**"
                          , "- Type: `" <> ppPrint ty <> ":" <> ppPrint (TST.getKind ty) <> "`"
                          ]
      CnsRep -> T.unlines [ "#### " <> ppPrint ns <> " destructor"
                          , "- **Left-Intro**"
                          , "- Type: `" <> ppPrint ty <> ":" <> ppPrint (TST.getKind ty) <> "`"
                          ]

xcaseToHoverMap :: Loc -> PrdCnsRep pc -> TST.Typ pol -> RST.NominalStructural -> HoverMap
xcaseToHoverMap loc pc ty ns = mkHoverMap loc msg
  where
    msg :: Text
    msg = case pc of
      PrdRep -> T.unlines [ "#### " <> ppPrint ns <> " cocase"
                          , "- **Right-Intro**"
                          , "- Type: `" <> ppPrint ty <> ":" <> ppPrint (TST.getKind ty) <> "`"
                          ]
      CnsRep -> T.unlines [ "#### " <> ppPrint ns <> " case"
                          , "- **Left-Intro**"
                          , "- Type: `" <> ppPrint ty <> ":" <> ppPrint (TST.getKind ty) <> "`"
                          ]

muAbsToHoverMap :: Loc -> PrdCnsRep pc -> TST.Typ pol -> HoverMap
muAbsToHoverMap loc pc ty = mkHoverMap loc msg
  where
    msg :: Text
    msg = case pc of
      PrdRep -> T.unlines [ "#### μ-Abstraction"
                          , "- Type: `" <> ppPrint ty <> ":" <> ppPrint (TST.getKind ty) <> "`"
                          ]
      CnsRep -> T.unlines [ "#### ~μ-Abstraction"
                          , "- Type: `" <> ppPrint ty <> ":" <> ppPrint (TST.getKind ty) <> "`"
                ]


dtorToHoverMap :: Loc -> TST.Typ pol -> RST.NominalStructural -> HoverMap
dtorToHoverMap loc ty ns = mkHoverMap loc msg
  where
    msg :: Text
    msg = T.unlines [ "#### " <> ppPrint ns <> " destructor application"
                    , "- **Right-Elim**"
                    , "- Type: `" <> ppPrint ty <> ":"<> ppPrint (TST.getKind ty) <> "`"
                    ]

lambdaToHoverMap :: Loc -> TST.Typ pol -> HoverMap
lambdaToHoverMap loc ty = mkHoverMap loc msg
  where
    msg :: Text
    msg = T.unlines [ "#### " <>  " lambda"
                    , "- **Right-Elim**"
                    , "- Type: `" <> ppPrint ty <> ":" <> ppPrint (TST.getKind ty) <> "`"
                    ]


caseToHoverMap :: Loc -> TST.Typ pol -> RST.NominalStructural -> HoverMap
caseToHoverMap loc ty ns = mkHoverMap loc msg
  where
    msg :: Text
    msg = T.unlines [ "#### " <> ppPrint ns <> " case-of"
                    , "- **Right-Elim**"
                    , "- Type: `" <> ppPrint ty <> ":" <> ppPrint (TST.getKind ty) <> "`"
                    ]

cocaseToHoverMap :: Loc -> TST.Typ pol -> RST.NominalStructural -> HoverMap
cocaseToHoverMap loc ty ns = mkHoverMap loc msg
  where
    msg :: Text
    msg = T.unlines [ "#### " <> ppPrint ns <> " cocase"
                    , "- **Right-Intro**"
                    , "- Type: `" <> ppPrint ty <> ":" <> ppPrint (TST.getKind ty) <> "`"
                    ]


methodToHoverMap :: Loc -> MethodName -> ClassName -> TST.InstanceResolved -> HoverMap
methodToHoverMap _ _ _ (TST.InstanceUnresolved _) = mempty
methodToHoverMap loc mn cn (TST.InstanceResolved inst) = mkHoverMap loc msg
  where
    msg :: Text
    msg = T.unlines [ "#### Type class method " <> ppPrint mn
                    , "- Defined in class: `" <> ppPrint cn <> "`"
                    , "- Resolved instance: `" <> ppPrint inst <> "`"
                    ]

instance ToHoverMap (Term pc) where
  toHoverMap (BoundVar loc _ ty _) =
    boundVarToHoverMap loc ty
  toHoverMap (FreeVar loc _ ty _) =
    freeVarToHoverMap loc ty
  toHoverMap (RawXtor loc pc ty ns _ args) =
    M.unions [xtorToHoverMap loc pc ty ns, toHoverMap args]
  toHoverMap (RawCase loc pc ty ns cases) =
    M.unions $ xcaseToHoverMap loc pc ty ns : (toHoverMap <$> cases)
  toHoverMap (RawMuAbs loc pc ty _ cmd) =
    M.unions [muAbsToHoverMap loc pc ty, toHoverMap cmd]
  toHoverMap (Dtor loc _ ty ns _ e (MkSubstitutionI (s1,_,s2))) =
    M.unions $ [dtorToHoverMap loc ty ns] <> (toHoverMap <$> (PrdTerm e:(s1 ++ s2)))
  toHoverMap (CaseOf loc _ ty ns e cases) =
    M.unions $ [caseToHoverMap loc ty ns] <> (toHoverMap <$> cases) <> [toHoverMap e]
  toHoverMap (XCaseI loc _pcrep PrdRep ty ns cocases) =
    M.unions $ [cocaseToHoverMap loc ty ns] <> (toHoverMap <$> cocases)
  toHoverMap (Lambda loc _pc ty _fvs tm) =
    M.unions $ [lambdaToHoverMap loc ty ] <> [toHoverMap tm]
  toHoverMap (PrimLitI64 loc _) =
    mkHoverMap loc $ T.unlines [ "#### Literal"
                               , "- Raw `#I64` literal"
                               ]
  toHoverMap (PrimLitF64 loc _) =
    mkHoverMap loc $ T.unlines [ "#### Literal"
                               , "- Raw `#F64` literal"
                               ]
  toHoverMap (PrimLitChar loc _) =
    mkHoverMap loc $ T.unlines [ "#### Literal"
                               , "- Raw `#Char` literal"
                               ]
  toHoverMap (PrimLitString loc _) =
    mkHoverMap loc $ T.unlines [ "#### Literal"
                               , "- Raw `#String` literal"
                               ]
  toHoverMap (XCaseI loc _pcrep CnsRep ty ns tmcasesI) =
    M.unions $ [cocaseToHoverMap loc ty ns] <> (toHoverMap <$> tmcasesI)
  toHoverMap (Semi loc _ ty ns _ (MkSubstitutionI (s1,_,s2)) t) =
    M.unions $ [cocaseToHoverMap loc ty ns] <> (toHoverMap <$> (CnsTerm t:(s1 ++ s2)))
  toHoverMap (CocaseOf loc _ ty ns t tmcasesI) =
    M.unions $ [cocaseToHoverMap loc ty ns] <> (toHoverMap <$> tmcasesI) <> [toHoverMap t]

instance ToHoverMap PrdCnsTerm where
  toHoverMap (PrdTerm tm) = toHoverMap tm
  toHoverMap (CnsTerm tm) = toHoverMap tm

applyToHoverMap :: Range -> AnyKind -> HoverMap
applyToHoverMap rng cc = M.fromList [(rng, mkHover (ppPrint cc) rng)]

instance ToHoverMap TST.Command where
  toHoverMap (RawApply loc kind prd cns) =
    M.unions [toHoverMap prd, toHoverMap cns, applyToHoverMap (locToRange loc) kind]
  toHoverMap (Print _ prd cmd) =
    M.unions [toHoverMap prd, toHoverMap cmd]
  toHoverMap (Read _ cns) = toHoverMap cns
  toHoverMap Jump {} = M.empty
  toHoverMap ExitSuccess {} = M.empty
  toHoverMap ExitFailure {} = M.empty
  toHoverMap PrimOp {} = M.empty
  toHoverMap (Method loc mn cn inst _ty subst) = M.union (methodToHoverMap loc mn cn inst) (toHoverMap subst)
  toHoverMap (CaseOfCmd _ _ t cmdcases) =
    M.unions $ toHoverMap t : map toHoverMap cmdcases
  toHoverMap (CaseOfI _ _ _ t tmcasesI) =
    M.unions $ toHoverMap t : map toHoverMap tmcasesI
  toHoverMap (CocaseOfCmd _ _ t cmdcases) =
    M.unions $ toHoverMap t : map toHoverMap cmdcases
  toHoverMap (CocaseOfI _ _ _ t tmcasesI) =
    M.unions $ toHoverMap t : map toHoverMap tmcasesI

instance ToHoverMap Substitution where
  toHoverMap subst = M.unions (toHoverMap <$> subst.unSubstitution)

---------------------------------------------------------------------------------
-- Converting a type to a HoverMap
---------------------------------------------------------------------------------

instance ToHoverMap (TST.PrdCnsType pol) where
 toHoverMap (TST.PrdCnsType _ ty) = toHoverMap ty

instance ToHoverMap (TST.LinearContext pol) where
  toHoverMap ctxt = M.unions $ toHoverMap <$> ctxt

instance ToHoverMap (TST.XtorSig pol) where
  toHoverMap sig = toHoverMap sig.sig_args

instance ToHoverMap [TST.XtorSig pol] where 
  toHoverMap lst = M.unions (map toHoverMap lst)

instance ToHoverMap (TST.VariantType pol) where
  toHoverMap (TST.CovariantType ty) = toHoverMap ty
  toHoverMap (TST.ContravariantType ty) = toHoverMap ty

prettyPolRep :: PolarityRep pol -> Text
prettyPolRep PosRep = "**+**"
prettyPolRep NegRep = "**-**"

instance ToHoverMap (TST.Typ pol) where
  toHoverMap (TST.TySkolemVar loc rep _knd var) =
    let
      msg = T.unlines [ "### Skolem Variable "
                        , "- Name: `" <> ppPrint var <> "`"
                        , "- Polarity: " <> prettyPolRep rep
                        , "- Kind: " <> ppPrint _knd
                      ]
    in
      mkHoverMap loc msg
  toHoverMap (TST.TyUniVar loc rep _knd var) =
    let
      msg = T.unlines [ "#### Unification variable "
                      , "- Name: `" <> ppPrint var <> "`"
                      , "- Polarity: " <> prettyPolRep rep
                      , "- Kind: " <> ppPrint _knd
                      ]
    in
      mkHoverMap loc msg
  toHoverMap (TST.TyRecVar loc rep _knd var) =
    let
      msg = T.unlines [ "#### Recursive variable "
                      , "- Name: `" <> ppPrint var <> "`"
                      , "- Polarity: " <> prettyPolRep rep
                      , "- Kind: " <> ppPrint _knd
                      ]
    in
      mkHoverMap loc msg

  toHoverMap (TST.TyData loc rep _knd xtors) =
    let
      msg = T.unlines [ "#### Structural data type"
                      , "- Polarity: " <> prettyPolRep rep
                      , "- Kind: " <> ppPrint _knd
                      ]
    in
      M.unions (mkHoverMap loc msg : (toHoverMap <$> xtors))
  toHoverMap (TST.TyDataRefined loc rep _knd tn xtors) =
    let
      msg = T.unlines [ "#### Refinement datatype"
                      , "- Name: `" <> ppPrint tn <> "`"
                      , "- Polarity: " <> prettyPolRep rep
                      , "- Kind: " <> ppPrint _knd
                      ]
    in
      M.unions (mkHoverMap loc msg : (toHoverMap <$> xtors))
  toHoverMap (TST.TyCodata loc rep _knd xtors) =
    let
      msg = T.unlines [ "#### Structural codata type"
                      , "- Polarity: " <> prettyPolRep rep
                      , "- Kind: " <> ppPrint _knd
                      ]
    in
      M.unions (mkHoverMap loc msg : (toHoverMap <$> xtors))
  toHoverMap (TST.TyCodataRefined loc rep _knd tn xtors) =
    let
      msg = T.unlines [ "#### Refinement codata type"
                      , "- Name: `" <> ppPrint tn <> "`"
                      , "- Polarity: " <> prettyPolRep rep
                      , "- Kind: " <> ppPrint _knd
                      ]
    in
      M.unions (mkHoverMap loc msg : (toHoverMap <$> xtors))
  toHoverMap (TST.TyNominal loc rep _knd tn) =
    let
      msg = T.unlines [ "#### Nominal type"
                      , "- Name: `" <> ppPrint tn <> "`"
                      , "- Doc: " <> maybe "" ppPrint tn.rnTnDoc
                      , "- Polarity: " <> prettyPolRep rep
                      , "- Kind: " <> ppPrint _knd
                      ]
    in
      mkHoverMap loc msg
  toHoverMap (TST.TyApp loc _ _ ty args) = 
    let 
      hoverTy = toHoverMap ty 
      betw = mkHoverMap loc (T.unlines ["applied to"])
      hoverArgs = toHoverMap <$> args
    in 
      M.unions ([hoverTy,betw]++NE.toList hoverArgs)
  toHoverMap (TST.TySyn loc rep nm ty) =
    let
      msg = T.unlines [ "#### Type synonym"
                      , "- Name: `" <> ppPrint nm <> "`"
                      , "- Doc: " <> maybe "" ppPrint nm.rnTnDoc
                      , "- Definition: `" <> ppPrint ty <> ":" <> ppPrint (TST.getKind ty) <> "`"
                      , "- Polarity: " <> prettyPolRep rep
                      ]
    in
      mkHoverMap loc msg
  toHoverMap (TST.TyTop loc _knd) =
    let
      msg = T.unlines [ "#### Top type"
                      , "- Polarity: " <> prettyPolRep NegRep
                      , "- Kind: " <> ppPrint _knd
                      ]
    in
      mkHoverMap loc msg
  toHoverMap (TST.TyBot loc _knd) =
    let
      msg = T.unlines [ "#### Bot type"
                      , "- Polarity: " <> prettyPolRep PosRep
                      , "- Kind: " <> ppPrint _knd
                      ]
    in
      mkHoverMap loc msg
  toHoverMap (TST.TyUnion loc _knd ty1 ty2) =
    let
      msg = T.unlines [ "#### Union type"
                      , "- Polarity: " <> prettyPolRep PosRep
                      , "- Kind: " <> ppPrint _knd
                      ]
    in
      M.unions [mkHoverMap loc msg, toHoverMap ty1, toHoverMap ty2]
  toHoverMap (TST.TyInter loc _knd ty1 ty2) =
    let
      msg = T.unlines [ "#### Intersection type"
                      , "- Polarity: " <> prettyPolRep NegRep
                      , "- Kind: " <> ppPrint _knd
                      ]
    in
      M.unions [mkHoverMap loc msg, toHoverMap ty1, toHoverMap ty2]
  toHoverMap (TST.TyRec loc rep _var ty) =
    let
      msg = T.unlines [ "#### Recursive type"
                      , "- Polarity: " <> prettyPolRep rep
                      , "- Type: " <> ppPrint ty <> ":" <> ppPrint (TST.getKind ty)
                      ]
    in
      M.union (mkHoverMap loc msg) (toHoverMap ty)
  toHoverMap (TST.TyI64 loc rep) =
    let
      msg = T.unlines [ "#### Primitive Type"
                      , "- Name: #I64"
                      , "- Polarity: " <> prettyPolRep rep
                      ]
    in
      mkHoverMap loc msg
  toHoverMap (TST.TyF64 loc rep) =
    let
      msg = T.unlines [ "#### Primitive Type"
                      , "- Name: #F64"
                      , "- Polarity: " <> prettyPolRep rep
                      ]
    in
      mkHoverMap loc msg
  toHoverMap (TST.TyChar loc rep) =
    let
      msg = T.unlines [ "#### Primitive Type"
                      , "- Name: #Char"
                      , "- Polarity: " <> prettyPolRep rep
                      ]
    in
      mkHoverMap loc msg
  toHoverMap (TST.TyString loc rep) =
    let
      msg = T.unlines [ "#### Primitive Type"
                      , "- Name: #String"
                      , "- Polarity: " <> prettyPolRep rep
                      ]
    in
      mkHoverMap loc msg
  toHoverMap (TST.TyFlipPol _ ty) = toHoverMap ty

 
instance ToHoverMap (TST.TypeScheme pol) where
  toHoverMap ts = toHoverMap ts.ts_monotype

---------------------------------------------------------------------------------
-- Converting declarations to a HoverMap
---------------------------------------------------------------------------------

instance ToHoverMap (TST.PrdCnsDeclaration pc) where
  toHoverMap decl =
    case decl.pcdecl_annot of
      TST.Inferred tys ->
            -- For an inferred type, we don't want to apply 'toHover' to tys, since it only contains
            -- defaultLoc.
            M.union (toHoverMap decl.pcdecl_term) (M.fromList [(locToRange decl.pcdecl_loc, mkHover (ppPrint tys) (locToRange decl.pcdecl_loc))])
      TST.Annotated tys -> 
            M.union (toHoverMap decl.pcdecl_term) (toHoverMap tys)

instance ToHoverMap TST.CommandDeclaration where
  toHoverMap decl=
    toHoverMap decl.cmddecl_cmd

instance ToHoverMap TST.DataDecl where
  toHoverMap decl@TST.NominalDecl {} = M.union (mkHoverMap decl.data_loc msg) (toHoverMap $ fst decl.data_xtors)
    where
      msg = T.unlines [ "#### Nominal " <> case decl.data_polarity of { Data -> "data"; Codata -> "codata"} <> " declaration",
                        "with polykind " <> ppPrint decl.data_kind
                      ]
  toHoverMap decl@TST.RefinementDecl {} = M.union (mkHoverMap decl.data_loc msg) (toHoverMap $ fst decl.data_xtors)
    where
      msg = T.unlines [ "#### Refinement " <> case decl.data_polarity of { Data -> "data"; Codata -> "codata"} <> " declaration" 
                      , "with polykind " <> ppPrint decl.data_kind
                      , " - Empty refinement type: " <> ppPrint (fst decl.data_refinement_empty)
                      , " - Full refinement type: " <> ppPrint (fst decl.data_refinement_full)
                      ]
      
instance ToHoverMap RST.StructuralXtorDeclaration where
  toHoverMap decl = mkHoverMap decl.strxtordecl_loc msg
    where
      msg = T.unlines [ "#### Structural " <> case decl.strxtordecl_xdata of { Data -> "constructor"; Codata -> "destructor"} <> " declaration"
                      , "with Arguments" <> argsToStr decl.strxtordecl_arity <> " and return Kind " <> ppPrint decl.strxtordecl_evalOrder
                      ]
      argsToStr :: [(PrdCns,MonoKind)] -> Text
      argsToStr [] = ""
      argsToStr ((Prd, mk):rst) = "Producer " <> ppPrint mk <> ", " <> argsToStr rst
      argsToStr ((Cns, mk):rst) = "Consumer " <> ppPrint mk <> ", " <> argsToStr rst

instance ToHoverMap CST.ImportDeclaration where
  toHoverMap decl = mkHoverMap decl.loc msg
    where
      msg = T.unlines [ "#### Module import"]

instance ToHoverMap CST.SetDeclaration where
  toHoverMap decl = mkHoverMap decl.loc msg
    where
      msg = T.unlines [ "#### Set option"]

instance ToHoverMap RST.TyOpDeclaration where
  toHoverMap decl = mkHoverMap decl.tyopdecl_loc msg
    where
      msg = T.unlines [ "#### Binary type operator"]

instance ToHoverMap RST.TySynDeclaration where
  toHoverMap decl = mkHoverMap decl.tysyndecl_loc msg
    where
      msg = T.unlines [ "#### Type synonym"]

instance ToHoverMap RST.ClassDeclaration where
  toHoverMap decl = mkHoverMap decl.classdecl_loc msg
    where
      msg = T.unlines [ "#### Type class"]

instance ToHoverMap TST.InstanceDeclaration where
  toHoverMap decl =
    M.unions $! toHoverMap <$> decl.instancedecl_cases

---------------------------------------------------------------------------------
-- Converting a program to a HoverMap
---------------------------------------------------------------------------------

instance ToHoverMap TST.Declaration where
  toHoverMap (TST.PrdCnsDecl _ decl) = toHoverMap decl
  toHoverMap (TST.CmdDecl decl)      = toHoverMap decl
  toHoverMap (TST.DataDecl decl)     = toHoverMap decl
  toHoverMap (TST.XtorDecl decl)     = toHoverMap decl
  toHoverMap (TST.ImportDecl decl)   = toHoverMap decl
  toHoverMap (TST.SetDecl decl)      = toHoverMap decl
  toHoverMap (TST.TyOpDecl decl)     = toHoverMap decl
  toHoverMap (TST.TySynDecl decl)    = toHoverMap decl
  toHoverMap (TST.ClassDecl decl)    = toHoverMap decl
  toHoverMap (TST.InstanceDecl decl) = toHoverMap decl

instance ToHoverMap TST.Module where
  toHoverMap mod = M.unions (toHoverMap <$> mod.mod_decls)
