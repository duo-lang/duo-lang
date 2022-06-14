module Translate.Focusing
  ( focusProgram
  , focusTerm
  , focusCmd
  , focusEnvironment
  , isFocusedTerm
  , isFocusedCmd
  ) where

import Data.Text qualified as T

import Eval.Definition (EvalEnv)
import Syntax.TST.Program
import Syntax.Common
import Syntax.TST.Terms
import Utils
import Syntax.Common.TypesPol (Typ(..))
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

isFocusedCmdCase :: EvaluationOrder -> CmdCase -> Maybe CmdCase
isFocusedCmdCase eo (MkCmdCase loc pat cmd) = MkCmdCase loc pat <$> isFocusedCmd eo cmd

-- | Check whether given command follows the focusing discipline.
isFocusedCmd :: EvaluationOrder -> Command -> Maybe Command
isFocusedCmd eo (Apply loc _annot _kind prd cns) = Apply loc ApplyAnnotOrig (Just (CBox eo)) <$> isFocusedTerm eo prd <*> isFocusedTerm eo cns
isFocusedCmd _  (ExitSuccess loc)          = Just (ExitSuccess loc)
isFocusedCmd _  (ExitFailure loc)          = Just (ExitFailure loc)
isFocusedCmd _  (Jump loc fv)              = Just (Jump loc fv)
isFocusedCmd eo (Print loc prd cmd)        = Print loc <$> isValueTerm eo PrdRep prd <*> isFocusedCmd eo cmd
isFocusedCmd eo (Read loc cns)             = Read loc <$> isValueTerm eo CnsRep cns
isFocusedCmd eo (PrimOp loc pt op subst)   = PrimOp loc pt op <$> isValueSubst eo subst

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

focusTerm :: EvaluationOrder  -> Term pc -> Term pc
-- If the term is already focused, we don't want to do anything
focusTerm eo (isFocusedTerm eo -> Just tm)   = tm
focusTerm _  (BoundVar loc rep ty var)          = BoundVar loc rep ty var
focusTerm _  (FreeVar loc rep ty var)           = FreeVar loc rep ty var
focusTerm eo (Xtor _ _annot pcrep ty ns xt subst) = focusXtor eo pcrep ty ns xt subst
focusTerm eo (XCase loc _annot rep ty ns cases) = XCase loc MatchAnnotOrig rep ty ns (focusCmdCase eo <$> cases)
focusTerm eo (MuAbs loc _annot rep ty v cmd)     = MuAbs loc MuAnnotOrig rep ty v (focusCmd eo cmd)
focusTerm _ (PrimLitI64 loc i)               = PrimLitI64 loc i
focusTerm _ (PrimLitF64 loc d)               = PrimLitF64 loc d


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
focusXtor :: EvaluationOrder -> PrdCnsRep pc ->  Typ (PrdCnsToPol pc) -> NominalStructural -> XtorName -> Substitution -> Term pc
focusXtor eo PrdRep ty ns xt subst =
    MuAbs defaultLoc MuAnnotOrig PrdRep ty Nothing (commandClosing [(Cns, alphaVar)] (shiftCmd ShiftUp (focusXtor' eo PrdRep ty ns xt subst [])))
focusXtor eo CnsRep ty ns xt subst =
    MuAbs defaultLoc MuAnnotOrig CnsRep ty Nothing (commandClosing [(Prd, alphaVar)] (shiftCmd ShiftUp (focusXtor' eo CnsRep ty ns xt subst [])))


focusXtor' :: EvaluationOrder -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) ->  NominalStructural -> XtorName -> [PrdCnsTerm] -> [PrdCnsTerm] -> Command
focusXtor' eo CnsRep ty ns xt [] pcterms' = Apply defaultLoc ApplyAnnotOrig  (Just (CBox eo)) (FreeVar defaultLoc PrdRep (TyFlipPol PosRep ty) alphaVar)
                                                                           (Xtor defaultLoc XtorAnnotOrig CnsRep ty ns xt (reverse pcterms'))
focusXtor' eo PrdRep ty ns xt [] pcterms' = Apply defaultLoc ApplyAnnotOrig  (Just (CBox eo)) (Xtor defaultLoc XtorAnnotOrig PrdRep ty ns xt (reverse pcterms'))
                                                                           (FreeVar defaultLoc CnsRep (TyFlipPol NegRep ty) alphaVar)
focusXtor' eo pc     ty ns xt (PrdTerm (isValueTerm eo PrdRep -> Just prd):pcterms) pcterms' = focusXtor' eo pc ty ns xt pcterms (PrdTerm prd : pcterms')
focusXtor' eo pc     ty ns xt (PrdTerm                                 prd:pcterms) pcterms' =
                                                              let
                                                                  var = betaVar (length pcterms') -- OK?
                                                                  tprd = getTypeTerm prd
                                                                  cmd = commandClosing [(Prd,var)]  (shiftCmd ShiftUp (focusXtor' eo pc ty ns xt pcterms (PrdTerm (FreeVar defaultLoc PrdRep tprd var) : pcterms')))
                                                              in
                                                                  Apply defaultLoc ApplyAnnotOrig  (Just (CBox eo)) (focusTerm eo prd) (MuAbs defaultLoc MuAnnotOrig CnsRep (TyFlipPol NegRep tprd) Nothing cmd)
focusXtor' eo pc     ty ns xt (CnsTerm (isValueTerm eo CnsRep -> Just cns):pcterms) pcterms' = focusXtor' eo pc ty ns xt pcterms (CnsTerm cns : pcterms')
focusXtor' eo pc     ty ns xt (CnsTerm                                 cns:pcterms) pcterms' =
                                                              let
                                                                  var = betaVar (length pcterms') -- OK?
                                                                  tcns = getTypeTerm cns
                                                                  cmd = commandClosing [(Cns,var)] (shiftCmd ShiftUp (focusXtor' eo pc ty ns xt pcterms (CnsTerm (FreeVar defaultLoc CnsRep tcns var) : pcterms')))
                                                              in Apply defaultLoc ApplyAnnotOrig  (Just (CBox eo)) (MuAbs defaultLoc MuAnnotOrig PrdRep (TyFlipPol PosRep tcns) Nothing cmd) (focusTerm eo cns)



focusCmdCase :: EvaluationOrder -> CmdCase -> CmdCase
focusCmdCase eo MkCmdCase { cmdcase_pat = XtorPat loc xt args, cmdcase_cmd } =
    MkCmdCase defaultLoc (XtorPat loc xt ((\(pc,_) -> (pc, Nothing)) <$> args)) (focusCmd eo cmdcase_cmd)


focusPrimOp :: EvaluationOrder -> (PrimitiveType, PrimitiveOp) -> [PrdCnsTerm] -> [PrdCnsTerm] -> Command
focusPrimOp _  (pt, op) [] pcterms' = PrimOp defaultLoc pt op (reverse pcterms')
focusPrimOp eo op (PrdTerm (isValueTerm eo PrdRep -> Just prd):pcterms) pcterms' = focusPrimOp eo op pcterms (PrdTerm prd : pcterms')
focusPrimOp eo op (PrdTerm prd:pcterms) pcterms' =
    let
        var = betaVar (length pcterms')
        cmd = commandClosing [(Prd,var)]  (shiftCmd ShiftUp (focusPrimOp eo op pcterms (PrdTerm (FreeVar defaultLoc PrdRep (getTypeTerm prd) var) : pcterms')))
    in
        Apply defaultLoc ApplyAnnotOrig (Just (CBox eo)) (focusTerm eo prd) (MuAbs defaultLoc MuAnnotOrig CnsRep (TyFlipPol NegRep (getTypeTerm prd)) Nothing cmd)
focusPrimOp eo op (CnsTerm (isValueTerm eo CnsRep -> Just cns):pcterms) pcterms' = focusPrimOp eo op pcterms (CnsTerm cns : pcterms')
focusPrimOp eo op (CnsTerm cns:pcterms) pcterms' =
    let
        var = betaVar (length pcterms')
        cmd = commandClosing [(Cns,var)] (shiftCmd ShiftUp (focusPrimOp eo op pcterms (CnsTerm (FreeVar defaultLoc CnsRep (getTypeTerm cns) var) : pcterms')))
    in
        Apply defaultLoc ApplyAnnotOrig  (Just (CBox eo)) (MuAbs defaultLoc MuAnnotOrig PrdRep (TyFlipPol PosRep (getTypeTerm cns)) Nothing cmd) (focusTerm eo cns)

-- | Invariant:
-- The output should have the property `isFocusedCmd cmd`.
focusCmd :: EvaluationOrder -> Command -> Command
focusCmd eo (Apply loc _annot _kind prd cns) = Apply loc ApplyAnnotOrig (Just (CBox eo)) (focusTerm eo prd) (focusTerm eo cns)
focusCmd _  (ExitSuccess loc) = ExitSuccess loc
focusCmd _  (ExitFailure loc) = ExitFailure loc
focusCmd _  (Jump loc fv) = Jump loc fv
focusCmd eo (Print loc (isValueTerm eo PrdRep -> Just prd) cmd) = Print loc prd (focusCmd eo cmd)
focusCmd eo (Print loc prd cmd) = Apply loc ApplyAnnotOrig (Just (CBox eo)) (focusTerm eo prd)
                                                             (MuAbs loc MuAnnotOrig CnsRep (TyFlipPol NegRep (getTypeTerm prd)) Nothing (Print loc (BoundVar loc PrdRep (getTypeTerm prd) (0,0)) (focusCmd eo cmd)))
focusCmd eo (Read loc (isValueTerm eo CnsRep -> Just cns)) = Read loc cns
focusCmd eo (Read loc cns) = Apply loc ApplyAnnotOrig (Just (CBox eo)) (MuAbs loc MuAnnotOrig PrdRep (TyFlipPol PosRep (getTypeTerm cns)) Nothing (Read loc (BoundVar loc CnsRep (getTypeTerm cns) (0,0))))
                                                        (focusTerm eo cns)
focusCmd eo (PrimOp _ pt op subst) = focusPrimOp eo (pt, op) subst []

---------------------------------------------------------------------------------
-- Lift Focusing to programs
---------------------------------------------------------------------------------
focusPrdCnsDeclaration :: EvaluationOrder -> PrdCnsDeclaration pc -> PrdCnsDeclaration pc
focusPrdCnsDeclaration eo MkPrdCnsDeclaration { pcdecl_loc, pcdecl_doc, pcdecl_pc, pcdecl_isRec, pcdecl_name, pcdecl_annot, pcdecl_term } =
    MkPrdCnsDeclaration { pcdecl_loc = pcdecl_loc
                        , pcdecl_doc = pcdecl_doc
                        , pcdecl_pc = pcdecl_pc
                        , pcdecl_isRec = pcdecl_isRec
                        , pcdecl_name = pcdecl_name
                        , pcdecl_annot = pcdecl_annot
                        , pcdecl_term = focusTerm eo pcdecl_term
                        }

focusCommandDeclaration :: EvaluationOrder -> CommandDeclaration -> CommandDeclaration
focusCommandDeclaration eo MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd } =
    MkCommandDeclaration { cmddecl_loc = cmddecl_loc
                         , cmddecl_doc = cmddecl_doc
                         , cmddecl_name = cmddecl_name
                         , cmddecl_cmd = focusCmd eo cmddecl_cmd
                         }

focusDecl :: EvaluationOrder -> Declaration -> Declaration
focusDecl eo (PrdCnsDecl pcrep decl) = PrdCnsDecl pcrep (focusPrdCnsDeclaration eo decl)
focusDecl eo (CmdDecl decl)          = CmdDecl (focusCommandDeclaration eo decl)
focusDecl _  decl@DataDecl {}        = decl
focusDecl _  decl@XtorDecl {}        = decl
focusDecl _  decl@ImportDecl {}      = decl
focusDecl _  decl@SetDecl {}         = decl
focusDecl _  decl@TyOpDecl {}        = decl
focusDecl _  decl@TySynDecl {}       = decl

focusProgram :: EvaluationOrder -> Program -> Program
focusProgram eo = fmap (focusDecl eo)

focusEnvironment :: EvaluationOrder -> EvalEnv -> EvalEnv
focusEnvironment cc (prd, cns, cmd) = (prd', cns', cmd')
  where
      prd' = focusTerm cc <$> prd
      cns' = focusTerm cc <$> cns
      cmd' = focusCmd cc <$> cmd
