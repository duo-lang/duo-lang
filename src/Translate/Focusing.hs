module Translate.Focusing
  ( Focus(..)
  , isFocusedTerm
  , isFocusedCmd
  ) where

import Data.Text qualified as T

import Eval.Definition (EvalEnv)
import Syntax.TST.Program
import Syntax.TST.Terms
import Syntax.TST.Types
import Syntax.RST.Types (PolarityRep(..))
import Syntax.RST.Terms qualified as RST
import Loc
import Syntax.CST.Terms qualified as CST
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
import Syntax.RST.Program (PrdCnsToPol)
import Syntax.CST.Kinds
import Syntax.CST.Names
import Syntax.Core.Annot
import qualified Syntax.LocallyNameless as LN

---------------------------------------------------------------------------------
-- Check whether terms are focused, values or covalues
---------------------------------------------------------------------------------

-- | Check whether given sterms is substitutable.
isValueTerm :: EvaluationOrder -> PrdCnsRep pc -> Term pc -> Maybe (Term pc)
isValueTerm CBV PrdRep FreeVar {}        = Nothing
isValueTerm CBN PrdRep fv@FreeVar {}   = Just fv
isValueTerm CBV CnsRep fv@FreeVar {}   = Just fv
isValueTerm CBN CnsRep FreeVar {}      = Nothing
isValueTerm CBV PrdRep MuAbs {}          = Nothing              -- CBV: so Mu is not a value.
isValueTerm CBV CnsRep (MuAbs loc _annot pc ty v cmd) = do
    cmd' <- isFocusedCmd CBV cmd -- CBV: so Mu~ is always a Value.
    pure $ MuAbs loc MuAnnotOrig pc ty v cmd'
isValueTerm CBN PrdRep (MuAbs loc _annot pc v ty cmd) = do
    cmd' <- isFocusedCmd CBN cmd -- CBN: so Mu is always a value.
    pure $ MuAbs loc MuAnnotOrig pc v ty cmd'
isValueTerm CBN CnsRep MuAbs {}          = Nothing              -- CBN: So Mu~ is not a value.
isValueTerm eo  _      tm                = isFocusedTerm eo tm

isValuePCTerm :: EvaluationOrder -> PrdCnsTerm -> Maybe PrdCnsTerm
isValuePCTerm eo (PrdTerm tm) = PrdTerm <$> isValueTerm eo PrdRep tm
isValuePCTerm eo (CnsTerm tm) = CnsTerm <$> isValueTerm eo CnsRep tm

-- | Check whether all arguments in the given argument list are substitutable.
isValueSubst :: EvaluationOrder -> Substitution -> Maybe Substitution
isValueSubst eo subst = sequence (isValuePCTerm eo <$> subst)

-- | Check whether given term follows the focusing discipline.
isFocusedTerm :: EvaluationOrder -> Term pc -> Maybe (Term pc)
isFocusedTerm _  bv@BoundVar {} = Just bv
isFocusedTerm _  fv@FreeVar {} = Just fv
isFocusedTerm eo (Xtor loc _annot pc ty ns xt subst) =
    Xtor loc XtorAnnotOrig pc ty ns xt <$> isValueSubst eo subst
isFocusedTerm eo (XCase loc _annot pc ty ns cases) =
    XCase loc MatchAnnotOrig pc ty ns <$> sequence (isFocusedCmdCase eo <$> cases)
isFocusedTerm eo (MuAbs loc _annot pc ty v cmd) =
    MuAbs loc MuAnnotOrig pc ty v <$> isFocusedCmd eo cmd
isFocusedTerm _  lit@PrimLitI64{} = Just lit
isFocusedTerm _  lit@PrimLitF64{} = Just lit
isFocusedTerm _  lit@PrimLitChar{} = Just lit
isFocusedTerm _  lit@PrimLitString{} = Just lit

isFocusedPCTerm :: EvaluationOrder -> PrdCnsTerm -> Maybe PrdCnsTerm
isFocusedPCTerm eo (PrdTerm tm) = PrdTerm <$> isFocusedTerm eo tm
isFocusedPCTerm eo (CnsTerm tm) = CnsTerm <$> isFocusedTerm eo tm

isFocusedSubst :: EvaluationOrder -> Substitution -> Maybe Substitution
isFocusedSubst eo subst = sequence (isFocusedPCTerm eo <$> subst)

isFocusedCmdCase :: EvaluationOrder -> CmdCase -> Maybe CmdCase
isFocusedCmdCase eo (MkCmdCase loc pat cmd) = MkCmdCase loc pat <$> isFocusedCmd eo cmd

-- | Check whether given command follows the focusing discipline.
isFocusedCmd :: EvaluationOrder -> Command -> Maybe Command
isFocusedCmd eo (Apply loc _annot _kind prd cns) = Apply loc ApplyAnnotOrig (CBox eo) <$> isFocusedTerm eo prd <*> isFocusedTerm eo cns
isFocusedCmd _  (ExitSuccess loc)          = Just (ExitSuccess loc)
isFocusedCmd _  (ExitFailure loc)          = Just (ExitFailure loc)
isFocusedCmd _  (Jump loc fv)              = Just (Jump loc fv)
isFocusedCmd eo (Method loc mn cn subst)   = Method loc mn cn <$> isFocusedSubst eo subst
isFocusedCmd eo (Print loc prd cmd)        = Print loc <$> isValueTerm eo PrdRep prd <*> isFocusedCmd eo cmd
isFocusedCmd eo (Read loc cns)             = Read loc <$> isValueTerm eo CnsRep cns
isFocusedCmd eo (PrimOp loc op subst)      = PrimOp loc op <$> isValueSubst eo subst

---------------------------------------------------------------------------------
-- The Focusing Algorithm
--
-- This focusing algorithm is similar to the algorithm presented in Figure 3.19
-- and 3.20 of the PhD thesis of Paul Downen, but generalized to work for arbitrary
-- data and codata types, and multiple evaluation orders.
-- Some optimizations are used to prevent the generation of excessive administrative
-- redexes.
--
-- We write [[t]] for the focusing translation of the term t.
--
-- Terms:
--
-- [[x]]                               := x
-- [[(co-)match { X Gamma => cmd }]]   := (co-)match { X Gamma => [[cmd]] }
-- [[mu x. cmd]]                       := mu x. [[cmd]]
-- [[X subst]]                         := X subst                           (if "X subst" is already focused)
-- [[X subst]]                         := focusXtor Prd/Cns X subst         (otherwise, see below)
--
-- Commands:
--
-- [[prd >> cns]]  := [[prd]] >> [[cns]]
-- [[ExitSuccess]] := ExitSuccess
-- [[ExitFailure]] := ExitFailure
-- [[Print(prd)]]  := ??? Unsure!
--
-- The `focusXtor` and `focusXtor'` function work together to focus a
-- xtor which has arguments which are not substitutable. We generate 1
-- fresh variable "alpha" for the entire term, and one additional fresh
-- variable "beta_i" for every term in the substitution which is not a value.
--
-- focusXtor Prd X subst := mu  alpha. (focusXtor' Prd X subst [])
-- focusXtor Cns X subst := mu~ alpha. (focusXtor' Cns X subst [])
--
-- writing "t" and "T" for unfocused and focused terms, the helper function
-- `focusXtor'`  works like this:
--
-- If we have transformed all arguments, we reconstruct the constructor application,
-- and apply it to the generated alpha:
--
-- focuxXtor' Prd X [] Ts := X Ts >> alpha
-- focusXtor' Cns X [] Ts := alpha >> X Ts
--
-- otherwise, we handle the next term from the substitution.
-- If the argument is already a value, we shuffle it to the RHS:
--
-- focusXtor' _ _ (T:ts) Ts := focusXtor' _ _ ts (T:Ts)
--
-- If the argument is not a value, we have to lift it:
--
-- focusXtor' _ _ (p:ts) Ts := [[p]] >> (mu~ beta_i. focusXtor' _ _ ts (beta_i:Ts))
-- focusXtor' _ _ (c:ts) Ts := (mu beta_i. focusXtor' _ _ ts (beta_i:Ts)) >> [[c]]
---------------------------------------------------------------------------------

class Focus a where
  focus :: EvaluationOrder -> a -> a

instance Focus (Term pc) where
  focus :: EvaluationOrder  -> Term pc -> Term pc
  -- If the term is already focused, we don't want to do anything
  focus eo (isFocusedTerm eo -> Just tm)   = tm
  focus _  (BoundVar loc rep ty var)          = BoundVar loc rep ty var
  focus _  (FreeVar loc rep ty var)           = FreeVar loc rep ty var
  focus eo (Xtor _ _annot pcrep ty ns xt subst) = focusXtor eo pcrep ty ns xt subst
  focus eo (XCase loc _annot rep ty ns cases) = XCase loc MatchAnnotOrig rep ty ns (focus eo <$> cases)
  focus eo (MuAbs loc _annot rep ty v cmd)     = MuAbs loc MuAnnotOrig rep ty v (focus eo cmd)
  focus _ (PrimLitI64 loc i)               = PrimLitI64 loc i
  focus _ (PrimLitF64 loc d)               = PrimLitF64 loc d
  focus _ (PrimLitChar loc d)              = PrimLitChar loc d
  focus _ (PrimLitString loc d)            = PrimLitString loc d

instance Focus PrdCnsTerm where
  focus :: EvaluationOrder -> PrdCnsTerm -> PrdCnsTerm
  focus eo (PrdTerm tm) = PrdTerm $ focus eo tm
  focus eo (CnsTerm tm) = CnsTerm $ focus eo tm

-- | The variable used for focusing the entire Xtor.
-- We use an unparseable name to guarantee that the name is fresh.
alphaVar :: FreeVarName
alphaVar = MkFreeVarName "$alpha"

-- | The variable used for focusing the individual arguments of the Xtor.
-- We use an unparseable name to guarantee that the name is fresh.
betaVar :: Int -> FreeVarName
betaVar i = MkFreeVarName ("$beta" <> T.pack (show i))

-- | Invariant of `focusXtor`:
--   The output should have the property `isFocusedSTerm`.
focusXtor :: EvaluationOrder -> PrdCnsRep pc ->  Typ (PrdCnsToPol pc) -> CST.NominalStructural -> XtorName -> Substitution -> Term pc
focusXtor eo PrdRep ty ns xt subst =
    MuAbs defaultLoc MuAnnotOrig PrdRep ty Nothing (LN.close [(Cns, alphaVar)] (LN.shift ShiftUp (focusXtor' eo PrdRep ty ns xt subst [])))
focusXtor eo CnsRep ty ns xt subst =
    MuAbs defaultLoc MuAnnotOrig CnsRep ty Nothing (LN.close [(Prd, alphaVar)] (LN.shift ShiftUp (focusXtor' eo CnsRep ty ns xt subst [])))


focusXtor' :: EvaluationOrder -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) ->  CST.NominalStructural -> XtorName -> [PrdCnsTerm] -> [PrdCnsTerm] -> Command
focusXtor' eo CnsRep ty ns xt [] pcterms' = Apply defaultLoc ApplyAnnotOrig  (CBox eo) (FreeVar defaultLoc PrdRep (TyFlipPol PosRep ty) alphaVar)
                                                                           (Xtor defaultLoc XtorAnnotOrig CnsRep ty ns xt (reverse pcterms'))
focusXtor' eo PrdRep ty ns xt [] pcterms' = Apply defaultLoc ApplyAnnotOrig  (CBox eo) (Xtor defaultLoc XtorAnnotOrig PrdRep ty ns xt (reverse pcterms'))
                                                                           (FreeVar defaultLoc CnsRep (TyFlipPol NegRep ty) alphaVar)
focusXtor' eo pc     ty ns xt (PrdTerm (isValueTerm eo PrdRep -> Just prd):pcterms) pcterms' = focusXtor' eo pc ty ns xt pcterms (PrdTerm prd : pcterms')
focusXtor' eo pc     ty ns xt (PrdTerm                                 prd:pcterms) pcterms' =
                                                              let
                                                                  var = betaVar (length pcterms') -- OK?
                                                                  tprd = getTypeTerm prd
                                                                  cmd = LN.close [(Prd,var)]  (LN.shift ShiftUp (focusXtor' eo pc ty ns xt pcterms (PrdTerm (FreeVar defaultLoc PrdRep tprd var) : pcterms')))
                                                              in
                                                                  Apply defaultLoc ApplyAnnotOrig  (CBox eo) (focus eo prd) (MuAbs defaultLoc MuAnnotOrig CnsRep (TyFlipPol NegRep tprd) Nothing cmd)
focusXtor' eo pc     ty ns xt (CnsTerm (isValueTerm eo CnsRep -> Just cns):pcterms) pcterms' = focusXtor' eo pc ty ns xt pcterms (CnsTerm cns : pcterms')
focusXtor' eo pc     ty ns xt (CnsTerm                                 cns:pcterms) pcterms' =
                                                              let
                                                                  var = betaVar (length pcterms') -- OK?
                                                                  tcns = getTypeTerm cns
                                                                  cmd = LN.close [(Cns,var)] (LN.shift ShiftUp (focusXtor' eo pc ty ns xt pcterms (CnsTerm (FreeVar defaultLoc CnsRep tcns var) : pcterms')))
                                                              in Apply defaultLoc ApplyAnnotOrig  (CBox eo) (MuAbs defaultLoc MuAnnotOrig PrdRep (TyFlipPol PosRep tcns) Nothing cmd) (focus eo cns)



instance Focus CmdCase where
  focus :: EvaluationOrder -> CmdCase -> CmdCase
  focus eo MkCmdCase { cmdcase_pat = XtorPat loc xt args, cmdcase_cmd } =
      MkCmdCase { cmdcase_loc = defaultLoc
                , cmdcase_pat = XtorPat loc xt ((\(pc,_) -> (pc, Nothing)) <$> args)
                , cmdcase_cmd = focus eo cmdcase_cmd}


instance Focus InstanceCase where
  focus :: EvaluationOrder -> InstanceCase -> InstanceCase
  focus eo MkInstanceCase { instancecase_pat = XtorPat loc xt args, instancecase_cmd } =
      MkInstanceCase { instancecase_loc = defaultLoc
                    , instancecase_pat = XtorPat loc xt ((\(pc,_) -> (pc, Nothing)) <$> args)
                    , instancecase_cmd = focus eo instancecase_cmd
                    }


focusPrimOp :: EvaluationOrder -> RST.PrimitiveOp -> [PrdCnsTerm] -> [PrdCnsTerm] -> Command
focusPrimOp _  op [] pcterms' = PrimOp defaultLoc op (reverse pcterms')
focusPrimOp eo op (PrdTerm (isValueTerm eo PrdRep -> Just prd):pcterms) pcterms' = focusPrimOp eo op pcterms (PrdTerm prd : pcterms')
focusPrimOp eo op (PrdTerm prd:pcterms) pcterms' =
    let
        var = betaVar (length pcterms')
        cmd = LN.close [(Prd,var)]  (LN.shift ShiftUp (focusPrimOp eo op pcterms (PrdTerm (FreeVar defaultLoc PrdRep (getTypeTerm prd) var) : pcterms')))
    in
        Apply defaultLoc ApplyAnnotOrig (CBox eo) (focus eo prd) (MuAbs defaultLoc MuAnnotOrig CnsRep (TyFlipPol NegRep (getTypeTerm prd)) Nothing cmd)
focusPrimOp eo op (CnsTerm (isValueTerm eo CnsRep -> Just cns):pcterms) pcterms' = focusPrimOp eo op pcterms (CnsTerm cns : pcterms')
focusPrimOp eo op (CnsTerm cns:pcterms) pcterms' =
    let
        var = betaVar (length pcterms')
        cmd = LN.close [(Cns,var)] (LN.shift ShiftUp (focusPrimOp eo op pcterms (CnsTerm (FreeVar defaultLoc CnsRep (getTypeTerm cns) var) : pcterms')))
    in
        Apply defaultLoc ApplyAnnotOrig  (CBox eo) (MuAbs defaultLoc MuAnnotOrig PrdRep (TyFlipPol PosRep (getTypeTerm cns)) Nothing cmd) (focus eo cns)

-- | Invariant:
-- The output should have the property `isFocusedCmd cmd`.
instance Focus Command where
  focus :: EvaluationOrder -> Command -> Command
  focus eo (Apply loc _annot _kind prd cns) = Apply loc ApplyAnnotOrig (CBox eo) (focus eo prd) (focus eo cns)
  focus _  (ExitSuccess loc) = ExitSuccess loc
  focus _  (ExitFailure loc) = ExitFailure loc
  focus _  (Jump loc fv) = Jump loc fv
  focus eo (Method loc mn cn subst) = Method loc mn cn (focus eo <$> subst)
  focus eo (Print loc (isValueTerm eo PrdRep -> Just prd) cmd) = Print loc prd (focus eo cmd)
  focus eo (Print loc prd cmd) = Apply loc ApplyAnnotOrig (CBox eo) (focus eo prd)
                                                              (MuAbs loc MuAnnotOrig CnsRep (TyFlipPol NegRep (getTypeTerm prd)) Nothing (Print loc (BoundVar loc PrdRep (getTypeTerm prd) (0,0)) (focus eo cmd)))
  focus eo (Read loc (isValueTerm eo CnsRep -> Just cns)) = Read loc cns
  focus eo (Read loc cns) = Apply loc ApplyAnnotOrig (CBox eo) (MuAbs loc MuAnnotOrig PrdRep (TyFlipPol PosRep (getTypeTerm cns)) Nothing (Read loc (BoundVar loc CnsRep (getTypeTerm cns) (0,0))))
                                                          (focus eo cns)
  focus eo (PrimOp _ op subst) = focusPrimOp eo op subst []

---------------------------------------------------------------------------------
-- Lift Focusing to programs
---------------------------------------------------------------------------------

instance Focus (PrdCnsDeclaration pc) where
  focus :: EvaluationOrder -> PrdCnsDeclaration pc -> PrdCnsDeclaration pc
  focus eo MkPrdCnsDeclaration { pcdecl_loc, pcdecl_doc, pcdecl_pc, pcdecl_isRec, pcdecl_name, pcdecl_annot, pcdecl_term } =
      MkPrdCnsDeclaration { pcdecl_loc = pcdecl_loc
                          , pcdecl_doc = pcdecl_doc
                          , pcdecl_pc = pcdecl_pc
                          , pcdecl_isRec = pcdecl_isRec
                          , pcdecl_name = pcdecl_name
                          , pcdecl_annot = pcdecl_annot
                          , pcdecl_term = focus eo pcdecl_term
                          }

instance Focus CommandDeclaration where
  focus :: EvaluationOrder -> CommandDeclaration -> CommandDeclaration
  focus eo MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd } =
      MkCommandDeclaration { cmddecl_loc = cmddecl_loc
                          , cmddecl_doc = cmddecl_doc
                          , cmddecl_name = cmddecl_name
                          , cmddecl_cmd = focus eo cmddecl_cmd
                          }

instance Focus InstanceDeclaration where
  focus :: EvaluationOrder -> InstanceDeclaration -> InstanceDeclaration
  focus eo MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_name, instancedecl_typ, instancedecl_cases } =
      MkInstanceDeclaration { instancedecl_loc
                            , instancedecl_doc
                            , instancedecl_name
                            , instancedecl_typ
                            , instancedecl_cases = focus eo <$> instancedecl_cases
                            }

instance Focus Declaration where
  focus :: EvaluationOrder -> Declaration -> Declaration
  focus eo (PrdCnsDecl pcrep decl) = PrdCnsDecl pcrep (focus eo decl)
  focus eo (CmdDecl decl)          = CmdDecl (focus eo decl)
  focus _  decl@DataDecl {}        = decl
  focus _  decl@XtorDecl {}        = decl
  focus _  decl@ImportDecl {}      = decl
  focus _  decl@SetDecl {}         = decl
  focus _  decl@TyOpDecl {}        = decl
  focus _  decl@TySynDecl {}       = decl
  focus _  decl@ClassDecl {}       = decl
  focus eo (InstanceDecl decl)     = InstanceDecl (focus eo decl)

instance Focus Module where
  focus :: EvaluationOrder -> Module -> Module
  focus eo mod@MkModule { mod_decls } =
      mod { mod_decls = focus eo <$> mod_decls }

instance Focus EvalEnv where
  focus :: EvaluationOrder -> EvalEnv -> EvalEnv
  focus cc (prd, cns, cmd) = (prd', cns', cmd')
    where
        prd' = focus cc <$> prd
        cns' = focus cc <$> cns
        cmd' = focus cc <$> cmd
