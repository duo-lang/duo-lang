module LSP.Handler.Hover
  ( hoverHandler
  , updateHoverCache
  ) where

import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.IORef (readIORef, modifyIORef)
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Text (Text)
import Language.LSP.Types
import Language.LSP.Server
    ( requestHandler, Handlers, getConfig )
import LSP.Definition ( LSPMonad, LSPConfig (MkLSPConfig), HoverMap, sendInfo )
import LSP.MegaparsecToLSP
import System.Log.Logger ( debugM )

import Pretty.Pretty ( ppPrint )
import Pretty.Common ()
import Pretty.Types ()
import Syntax.Common
import Syntax.TST.Terms hiding (Command)
import Syntax.TST.Terms qualified as TST
import Syntax.TST.Program qualified as TST
import Sugar.TST
import Syntax.Common.TypesPol
import Utils (Loc)

---------------------------------------------------------------------------------
-- Handle Type on Hover
---------------------------------------------------------------------------------

hoverHandler :: Handlers LSPMonad
hoverHandler = requestHandler STextDocumentHover $ \req responder ->  do
  let (RequestMessage _ _ _ (HoverParams (TextDocumentIdentifier uri) pos _)) = req
  liftIO $ debugM "lspserver.hoverHandler" ("Received hover request: " <> show uri <> " at: " <> show pos)
  MkLSPConfig ref <- getConfig
  cache <- liftIO $ readIORef ref
  case M.lookup uri cache of
    Nothing -> do
      sendInfo ("Hover Cache not initialized for: " <> T.pack (show uri))
      responder (Right Nothing)
    Just cache -> responder (Right (lookupInRangeMap pos cache))


updateHoverCache :: Uri -> TST.Program -> LSPMonad ()
updateHoverCache uri prog = do
  MkLSPConfig ref <- getConfig
  liftIO $ modifyIORef ref (M.insert uri (toHoverMap prog))

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
  toHoverMap MkTermCase {tmcase_term} = toHoverMap tmcase_term

instance ToHoverMap (TermCaseI pc) where
  toHoverMap MkTermCaseI {tmcasei_term} = toHoverMap tmcasei_term

instance ToHoverMap CmdCase where
  toHoverMap MkCmdCase {cmdcase_cmd} = toHoverMap cmdcase_cmd

instance ToHoverMap InstanceCase where
  toHoverMap MkInstanceCase {instancecase_cmd} = toHoverMap instancecase_cmd


boundVarToHoverMap :: Loc -> Typ pol -> HoverMap
boundVarToHoverMap loc ty = mkHoverMap loc msg
  where
    msg :: Text
    msg = T.unlines [ "#### Bound variable"
                    , "- Type: `" <> (ppPrint ty) <> "`"
                    ]

freeVarToHoverMap :: Loc -> Typ pol -> HoverMap
freeVarToHoverMap loc ty = mkHoverMap loc msg
  where
    msg :: Text
    msg = T.unlines [ "#### Free variable"
                    , "- Type: `" <> ppPrint ty <> "`"
                    ]

xtorToHoverMap :: Loc -> PrdCnsRep pc -> Typ pol -> NominalStructural -> HoverMap
xtorToHoverMap loc pc ty ns = mkHoverMap loc msg
  where
    msg :: Text
    msg = case pc of
      PrdRep -> T.unlines [ "#### " <> ppPrint ns <> " constructor"
                          , "- **Right-Intro**"
                          , "- Type: `" <> ppPrint ty <> "`"
                          ]
      CnsRep -> T.unlines [ "#### " <> ppPrint ns <> " destructor"
                          , "- **Left-Intro**"
                          , "- Type: `" <> ppPrint ty <> "`"
                          ]

xcaseToHoverMap :: Loc -> PrdCnsRep pc -> Typ pol -> NominalStructural -> HoverMap
xcaseToHoverMap loc pc ty ns = mkHoverMap loc msg
  where
    msg :: Text
    msg = case pc of
      PrdRep -> T.unlines [ "#### " <> ppPrint ns <> " cocase"
                          , "- **Right-Intro**"
                          , "- Type: `" <> ppPrint ty <> "`"
                          ]
      CnsRep -> T.unlines [ "#### " <> ppPrint ns <> " case"
                          , "- **Left-Intro**"
                          , "- Type: `" <> (ppPrint ty) <> "`"
                          ]

muAbsToHoverMap :: Loc -> PrdCnsRep pc -> Typ pol -> HoverMap
muAbsToHoverMap loc pc ty = mkHoverMap loc msg
  where
    msg :: Text
    msg = case pc of
      PrdRep -> T.unlines [ "#### μ-Abstraction"
                          , "- Type: `" <> ppPrint ty <> "`"
                          ]
      CnsRep -> T.unlines [ "#### ~μ-Abstraction"
                          , "- Type: `" <> ppPrint ty <> "`"
                          ]

dtorToHoverMap :: Loc -> Typ pol -> NominalStructural -> HoverMap
dtorToHoverMap loc ty ns = mkHoverMap loc msg
  where
    msg :: Text
    msg = T.unlines [ "#### " <> ppPrint ns <> " destructor application"
                    , "- **Right-Elim**"
                    , "- Type: `" <> ppPrint ty <> "`"
                    ]

lambdaToHoverMap :: Loc -> Typ pol ->  HoverMap
lambdaToHoverMap loc ty = mkHoverMap loc msg
  where
    msg :: Text
    msg = T.unlines [ "#### " <>  " lambda"
                    , "- **Right-Elim**"
                    , "- Type: `" <> ppPrint ty <> "`"
                    ]

caseToHoverMap :: Loc -> Typ pol -> NominalStructural -> HoverMap
caseToHoverMap loc ty ns = mkHoverMap loc msg
  where
    msg :: Text
    msg = T.unlines [ "#### " <> ppPrint ns <> " case-of"
                    , "- **Right-Elim**"
                    , "- Type: `" <> ppPrint ty <> "`"
                    ]

cocaseToHoverMap :: Loc -> Typ pol -> NominalStructural -> HoverMap
cocaseToHoverMap loc ty ns = mkHoverMap loc msg
  where
    msg :: Text
    msg = T.unlines [ "#### " <> ppPrint ns <> " cocase"
                    , "- **Right-Intro**"
                    , "- Type: `" <> ppPrint ty <> "`"
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
  toHoverMap (Dtor loc _ ty ns _ e (s1,_,s2)) =
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
  toHoverMap (XCaseI loc _pcrep CnsRep ty ns tmcasesI) =
    M.unions $ [cocaseToHoverMap loc ty ns] <> (toHoverMap <$> tmcasesI)
  toHoverMap (Semi loc _ ty ns _ (s1,_,s2) t) =
    M.unions $ [cocaseToHoverMap loc ty ns] <> (toHoverMap <$> (CnsTerm t:(s1 ++ s2)))
  toHoverMap (CocaseOf loc _ ty ns t tmcasesI) =
    M.unions $ [cocaseToHoverMap loc ty ns] <> (toHoverMap <$> tmcasesI) <> [toHoverMap t]

instance ToHoverMap PrdCnsTerm where
  toHoverMap (PrdTerm tm) = toHoverMap tm
  toHoverMap (CnsTerm tm) = toHoverMap tm

applyToHoverMap :: Range -> Maybe MonoKind -> HoverMap
applyToHoverMap rng Nothing   = M.fromList [(rng, mkHover "Kind not inferred" rng)]
applyToHoverMap rng (Just cc) = M.fromList [(rng, mkHover (ppPrint cc) rng)]

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
  toHoverMap (CaseOfCmd _ _ t cmdcases) =
    M.unions $ toHoverMap t : map toHoverMap cmdcases
  toHoverMap (CaseOfI _ _ _ t tmcasesI) =
    M.unions $ toHoverMap t : map toHoverMap tmcasesI
  toHoverMap (CocaseOfCmd _ _ t cmdcases) =
    M.unions $ toHoverMap t : map toHoverMap cmdcases
  toHoverMap (CocaseOfI _ _ _ t tmcasesI) =
    M.unions $ toHoverMap t : map toHoverMap tmcasesI

instance ToHoverMap Substitution where
  toHoverMap subst = M.unions (toHoverMap <$> subst)

---------------------------------------------------------------------------------
-- Converting a type to a HoverMap
---------------------------------------------------------------------------------

instance ToHoverMap (PrdCnsType pol) where
  toHoverMap (PrdCnsType _ ty) = toHoverMap ty

instance ToHoverMap (LinearContext pol) where
  toHoverMap ctxt = M.unions $ toHoverMap <$> ctxt

instance ToHoverMap (XtorSig pol) where
  toHoverMap MkXtorSig { sig_args } = toHoverMap sig_args

instance ToHoverMap (VariantType pol) where
  toHoverMap (CovariantType ty) = toHoverMap ty
  toHoverMap (ContravariantType ty) = toHoverMap ty

prettyPolRep :: PolarityRep pol -> Text
prettyPolRep PosRep = "**+**"
prettyPolRep NegRep = "**-**"

instance ToHoverMap (Typ pol) where
  toHoverMap (TySkolemVar loc rep _knd var) = 
    let 
      msg = T.unlines [ "### Skolem Variable "
                        , "- Name: `" <> ppPrint var <> "`"
                        , "-Polarity: " <> prettyPolRep rep
                      ]
    in
      mkHoverMap loc msg
  toHoverMap (TyUniVar loc rep _knd var) =
    let
      msg = T.unlines [ "#### Unification variable "
                      , "- Name: `" <> ppPrint var <> "`"
                      , "- Polarity: " <> prettyPolRep rep
                      ]
    in 
      mkHoverMap loc msg
  toHoverMap (TyRecVar loc rep _knd var) =
    let
      msg = T.unlines [ "#### Recursive variable "
                      , "- Name: `" <> ppPrint var <> "`"
                      , "- Polarity: " <> prettyPolRep rep
                      ]
    in 
      mkHoverMap loc msg

  toHoverMap (TyData loc rep xtors) =
    let
      msg = T.unlines [ "#### Structural data type"
                      , "- Polarity: " <> prettyPolRep rep
                      ]
    in
      M.unions ((mkHoverMap loc msg) : (toHoverMap <$> xtors))
  toHoverMap (TyDataRefined loc rep tn xtors) =
    let
      msg = T.unlines [ "#### Refinement datatype"
                      , "- Name: `" <> ppPrint tn <> "`"
                      , "- Polarity: " <> prettyPolRep rep
                      ]
    in
      M.unions ((mkHoverMap loc msg) : (toHoverMap <$> xtors))
  toHoverMap (TyCodata loc rep xtors) =
    let
      msg = T.unlines [ "#### Structural codata type"
                      , "- Polarity: " <> prettyPolRep rep
                      ]
    in
      M.unions ((mkHoverMap loc msg) : (toHoverMap <$> xtors))
  toHoverMap (TyCodataRefined loc rep tn xtors) =
    let
      msg = T.unlines [ "#### Refinement codata type"
                      , "- Name: `" <> ppPrint tn <> "`"
                      , "- Polarity: " <> prettyPolRep rep
                      ]
    in
      M.unions ((mkHoverMap loc msg) : (toHoverMap <$> xtors))
  toHoverMap (TyNominal loc rep _knd tn args) =
    let
      msg = T.unlines [ "#### Nominal type"
                      , "- Name: `" <> ppPrint tn <> "`"
                      , "- Doc: " <> maybe "" ppPrint (rnTnDoc tn)
                      , "- Polarity: " <> prettyPolRep rep
                      ]
    in
      M.unions ((mkHoverMap loc msg) : (toHoverMap <$> args))
  toHoverMap (TySyn loc rep nm ty) =
    let
      msg = T.unlines [ "#### Type synonym"
                      , "- Name: `" <> ppPrint nm <> "`"
                      , "- Doc: " <> maybe "" ppPrint (rnTnDoc nm)
                      , "- Definition: `" <> ppPrint ty <> "`"
                      , "- Polarity: " <> prettyPolRep rep
                      ]
    in
      mkHoverMap loc msg
  toHoverMap (TyTop loc _knd) =
    let
      msg = T.unlines [ "#### Top type"
                      , "- Polarity: " <> prettyPolRep NegRep
                      ]
    in
      mkHoverMap loc msg
  toHoverMap (TyBot loc _knd) =
    let
      msg = T.unlines [ "#### Bot type"
                      , "- Polarity: " <> prettyPolRep PosRep
                      ]
    in
      mkHoverMap loc msg
  toHoverMap (TyUnion loc _knd ty1 ty2) =
    let
      msg = T.unlines [ "#### Union type"
                      , "- Polarity: " <> prettyPolRep PosRep
                      ]
    in
      M.unions [mkHoverMap loc msg, toHoverMap ty1, toHoverMap ty2]
  toHoverMap (TyInter loc _knd ty1 ty2) =
    let
      msg = T.unlines [ "#### Intersection type"
                      , "- Polarity: " <> prettyPolRep NegRep
                      ]
    in
      M.unions [mkHoverMap loc msg, toHoverMap ty1, toHoverMap ty2]
  toHoverMap (TyRec loc rep _var ty) =
    let
      msg = T.unlines [ "#### Recursive type"
                      , "- Polarity: " <> prettyPolRep rep
                      ]
    in
      M.union (mkHoverMap loc msg) (toHoverMap ty)
  toHoverMap (TyI64 loc rep) =
    let
      msg = T.unlines [ "#### Primitive Type" 
                      , "- Name: #I64"
                      , "- Polarity: " <> prettyPolRep rep
                      ]
    in
      mkHoverMap loc msg
  toHoverMap (TyF64 loc rep) =
    let
      msg = T.unlines [ "#### Primitive Type" 
                      , "- Name: #F64"
                      , "- Polarity: " <> prettyPolRep rep
                      ]
    in
      mkHoverMap loc msg
  toHoverMap (TyFlipPol _ ty) = toHoverMap ty

instance ToHoverMap (TypeScheme pol) where
  toHoverMap (TypeScheme { ts_monotype }) = toHoverMap ts_monotype

---------------------------------------------------------------------------------
-- Converting a program to a HoverMap
---------------------------------------------------------------------------------

instance ToHoverMap (TST.PrdCnsDeclaration pc) where
  toHoverMap TST.MkPrdCnsDeclaration { pcdecl_loc, pcdecl_annot = Inferred tys, pcdecl_term } =
    -- For an inferred type, we don't want to apply 'toHover' to tys, since it only contains
    -- defaultLoc.
    M.union (toHoverMap pcdecl_term) (M.fromList [(locToRange pcdecl_loc, mkHover (ppPrint tys) (locToRange pcdecl_loc))])
  toHoverMap TST.MkPrdCnsDeclaration { pcdecl_annot = Annotated tys, pcdecl_term } =
    M.union (toHoverMap pcdecl_term) (toHoverMap tys)

instance ToHoverMap TST.CommandDeclaration where
  toHoverMap TST.MkCommandDeclaration { cmddecl_cmd } =
    toHoverMap cmddecl_cmd

instance ToHoverMap TST.InstanceDeclaration where
  toHoverMap TST.MkInstanceDeclaration { instancedecl_cases } =
    M.unions $! toHoverMap <$> instancedecl_cases

instance ToHoverMap TST.Declaration where
  toHoverMap (TST.PrdCnsDecl _ decl) = toHoverMap decl
  toHoverMap (TST.CmdDecl decl)  = toHoverMap decl
  toHoverMap (TST.DataDecl _decl) = M.empty
  toHoverMap (TST.XtorDecl _) = M.empty
  toHoverMap (TST.ImportDecl _) = M.empty
  toHoverMap (TST.SetDecl _) = M.empty
  toHoverMap (TST.TyOpDecl _) = M.empty
  toHoverMap (TST.TySynDecl _) = M.empty
  toHoverMap (TST.ClassDecl _decl) = M.empty
  toHoverMap (TST.InstanceDecl decl) = toHoverMap decl

instance ToHoverMap TST.Program where
  toHoverMap prog = M.unions (toHoverMap <$> prog)
