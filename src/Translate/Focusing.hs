module Translate.Focusing ( Focus(..) ) where

import Data.Text qualified as T

import Eval.Definition (EvalEnv)
import Syntax.TST.Program
import Syntax.TST.Terms
import Syntax.TST.Types
import Syntax.Core.Terms (Pattern(..))
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
import Data.Maybe (isNothing)
import Syntax.NMap (NMap(..), (<¢>))

---------------------------------------------------------------------------------
-- Check whether terms are focused, values or covalues
---------------------------------------------------------------------------------

-- | Check whether given sterms is substitutable.
isValueTerm :: PrdCnsRep pc -> Term pc -> Maybe (Term pc)
-- Free Variables:
isValueTerm PrdRep fv@(FreeVar _ _ ty _) = do
  let knd = getKind ty
  case knd of
    CBox CBV -> Nothing
    CBox CBN -> Just fv
    KindVar kv -> error ("Found unresolved KindVar " <> show kv <> "during focusing")
    I64Rep -> Just fv
    F64Rep -> Just fv
    CharRep -> Just fv
    StringRep -> Just fv
isValueTerm CnsRep fv@(FreeVar _ _ ty _) = do
  let knd = getKind ty
  case knd of
    CBox CBV -> Just fv
    CBox CBN -> Nothing
    KindVar kv -> error ("Found unresolved KindVar " <> show kv <> "during focusing")
    I64Rep -> Just fv
    F64Rep -> Just fv
    CharRep -> Just fv
    StringRep -> Just fv
-- Mu-Abstractions:
isValueTerm PrdRep (MuAbs loc annot pc ty v cmd) = do
  let knd = getKind ty
  case knd of
    CBox CBV -> Nothing -- CBV, so a Mu-Abstraction is never a value.
    CBox CBN -> do
      -- CBN, so we have to check whether the command is focused.
      cmd' <- isFocused cmd
      pure (MuAbs loc annot pc ty v cmd')
    KindVar kv -> error ("Found unresolved KindVar " <> show kv <> "during focusing")
    I64Rep -> error "Found Mu-Abstraction of kind I64Rep"
    F64Rep -> error "Found Mu-Abstraction of kind F64Rep"
    CharRep -> error "Found Mu-Abstraction of kind CharRep"
    StringRep -> error "Found Mu-Abstraction of kind StringRep"
-- ~Mu-Abstractions:
isValueTerm CnsRep (MuAbs loc annot pc ty v cmd) = do
  let knd = getKind ty
  case knd of
    CBox CBN -> Nothing -- CBN, so a ~Mu-Abstraction is never a value.
    CBox CBV -> do
      -- CBV, so we have to check whether the command is focused.
      cmd' <- isFocused cmd
      pure (MuAbs loc annot pc ty v cmd')
    KindVar kv -> error ("Found unresolved KindVar " <> show kv <> "during focusing")
    I64Rep -> Just (MuAbs loc annot pc ty v cmd)
    F64Rep -> Just (MuAbs loc annot pc ty v cmd)
    CharRep -> Just (MuAbs loc annot pc ty v cmd)
    StringRep -> Just (MuAbs loc annot pc ty v cmd)
isValueTerm _ tm = isFocused tm

isValuePCTerm :: PrdCnsTerm -> Maybe PrdCnsTerm
isValuePCTerm (PrdTerm tm) = PrdTerm <$> isValueTerm PrdRep tm
isValuePCTerm (CnsTerm tm) = CnsTerm <$> isValueTerm CnsRep tm

-- | Check whether all arguments in the given argument list are substitutable.
isValueSubst :: Substitution -> Maybe Substitution
isValueSubst = fmap MkSubstitution . mapM isValuePCTerm . unSubstitution

---------------------------------------------------------------------------------
-- A typeclass for focusing 
---------------------------------------------------------------------------------

-- | A typeclass for focusing AST types.
-- Law I: If `isFocused x = Just y`, then `focus x = x`.
-- Law II: `isFocused (focus x) = Just (focus x)`
-- Law III: `focus (focus x) = focus x`
class Focus a where
  focus :: a -> a
  isFocused :: a -> Maybe a

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

instance Focus (Term pc) where
  focus :: Term pc -> Term pc
  -- If the term is already focused, we don't want to do anything
  focus (isFocused -> Just tm) = tm
  focus (BoundVar loc rep ty var)            = BoundVar loc rep ty var
  focus (FreeVar loc rep ty var)             = FreeVar loc rep ty var
  focus (Xtor _ _annot pcrep ty ns xt subst) = focusXtor pcrep ty ns xt subst
  focus (XCase loc _annot rep ty ns cases)   = XCase loc MatchAnnotOrig rep ty ns (focus <$> cases)
  focus (MuAbs loc _annot rep ty v cmd)      = MuAbs loc MuAnnotOrig rep ty v (focus cmd)
  focus (PrimLitI64 loc i)                   = PrimLitI64 loc i
  focus (PrimLitF64 loc d)                   = PrimLitF64 loc d
  focus (PrimLitChar loc d)                  = PrimLitChar loc d
  focus (PrimLitString loc d)                = PrimLitString loc d

  isFocused :: Term pc -> Maybe (Term pc)
  isFocused bv@BoundVar {} = Just bv
  isFocused fv@FreeVar {} = Just fv
  isFocused (Xtor loc _annot pc ty ns xt subst) =
    Xtor loc XtorAnnotOrig pc ty ns xt <$> isValueSubst subst
  isFocused (XCase loc _annot pc ty ns cases) =
    XCase loc MatchAnnotOrig pc ty ns <$> mapM isFocused cases
  isFocused (MuAbs loc _annot pc ty v cmd) =
    MuAbs loc MuAnnotOrig pc ty v <$> isFocused cmd
  isFocused lit@PrimLitI64{} = Just lit
  isFocused lit@PrimLitF64{} = Just lit
  isFocused lit@PrimLitChar{} = Just lit
  isFocused lit@PrimLitString{} = Just lit

instance Focus PrdCnsTerm where
  focus :: PrdCnsTerm -> PrdCnsTerm
  focus (PrdTerm tm) = PrdTerm $ focus tm
  focus (CnsTerm tm) = CnsTerm $ focus tm

  isFocused :: PrdCnsTerm -> Maybe PrdCnsTerm
  isFocused (PrdTerm tm) = PrdTerm <$> isFocused tm
  isFocused (CnsTerm tm) = CnsTerm <$> isFocused tm

instance Focus Substitution where
  focus :: Substitution -> Substitution
  focus = nmap focus

  isFocused :: Substitution -> Maybe Substitution
  isFocused = nmapM isFocused

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
focusXtor :: PrdCnsRep pc ->  Typ (PrdCnsToPol pc) -> CST.NominalStructural -> XtorName -> Substitution -> Term pc
focusXtor PrdRep ty ns xt subst =
    MuAbs defaultLoc MuAnnotOrig PrdRep ty Nothing (LN.close [(Cns, alphaVar)] (LN.shift ShiftUp (focusXtor' PrdRep ty ns xt (unSubstitution subst) [])))
focusXtor CnsRep ty ns xt subst =
    MuAbs defaultLoc MuAnnotOrig CnsRep ty Nothing (LN.close [(Prd, alphaVar)] (LN.shift ShiftUp (focusXtor' CnsRep ty ns xt (unSubstitution subst) [])))


focusXtor' :: PrdCnsRep pc -> Typ (PrdCnsToPol pc) ->  CST.NominalStructural -> XtorName -> [PrdCnsTerm] -> [PrdCnsTerm] -> Command
focusXtor' CnsRep ty ns xt [] pcterms' = Apply defaultLoc ApplyAnnotOrig  (getKind ty) (FreeVar defaultLoc PrdRep (TyFlipPol PosRep ty) alphaVar)
                                                                           (Xtor defaultLoc XtorAnnotOrig CnsRep ty ns xt (MkSubstitution $ reverse pcterms'))
focusXtor' PrdRep ty ns xt [] pcterms' = Apply defaultLoc ApplyAnnotOrig  (getKind ty) (Xtor defaultLoc XtorAnnotOrig PrdRep ty ns xt (MkSubstitution $ reverse pcterms'))
                                                                           (FreeVar defaultLoc CnsRep (TyFlipPol NegRep ty) alphaVar)
focusXtor' pc     ty ns xt (PrdTerm (isValueTerm PrdRep -> Just prd):pcterms) pcterms' = focusXtor' pc ty ns xt pcterms (PrdTerm prd : pcterms')
focusXtor' pc     ty ns xt (PrdTerm                                 prd:pcterms) pcterms' =
                                                              let
                                                                  var = betaVar (length pcterms') -- OK?
                                                                  tprd = getTypeTerm prd
                                                                  cmd = LN.close [(Prd,var)]  (LN.shift ShiftUp (focusXtor' pc ty ns xt pcterms (PrdTerm (FreeVar defaultLoc PrdRep tprd var) : pcterms')))
                                                              in
                                                                  Apply defaultLoc ApplyAnnotOrig (getKind tprd) (focus prd) (MuAbs defaultLoc MuAnnotOrig CnsRep (TyFlipPol NegRep tprd) Nothing cmd)
focusXtor' pc     ty ns xt (CnsTerm (isValueTerm CnsRep -> Just cns):pcterms) pcterms' = focusXtor' pc ty ns xt pcterms (CnsTerm cns : pcterms')
focusXtor' pc     ty ns xt (CnsTerm                                 cns:pcterms) pcterms' =
                                                              let
                                                                  var = betaVar (length pcterms') -- OK?
                                                                  tcns = getTypeTerm cns
                                                                  cmd = LN.close [(Cns,var)] (LN.shift ShiftUp (focusXtor' pc ty ns xt pcterms (CnsTerm (FreeVar defaultLoc CnsRep tcns var) : pcterms')))
                                                              in Apply defaultLoc ApplyAnnotOrig  (getKind tcns) (MuAbs defaultLoc MuAnnotOrig PrdRep (TyFlipPol PosRep tcns) Nothing cmd) (focus cns)



instance Focus CmdCase where
  focus :: CmdCase -> CmdCase
  focus MkCmdCase { cmdcase_pat = XtorPat loc xt args, cmdcase_cmd } =
    MkCmdCase { cmdcase_loc = defaultLoc
              , cmdcase_pat = XtorPat loc xt ((\(pc,_) -> (pc, Nothing)) <$> args)
              , cmdcase_cmd = focus cmdcase_cmd
              }

  isFocused :: CmdCase -> Maybe CmdCase
  isFocused (MkCmdCase loc pat cmd) =
    MkCmdCase loc pat <$> isFocused cmd


instance Focus InstanceCase where
  focus :: InstanceCase -> InstanceCase
  focus MkInstanceCase { instancecase_pat = XtorPat loc xt args, instancecase_cmd } =
    MkInstanceCase { instancecase_loc = defaultLoc
                   , instancecase_pat = XtorPat loc xt ((\(pc,_) -> (pc, Nothing)) <$> args)
                   , instancecase_cmd = focus instancecase_cmd
                   }
  
  isFocused :: InstanceCase -> Maybe InstanceCase
  isFocused (MkInstanceCase loc pat cmd) =
    MkInstanceCase loc pat <$> isFocused cmd


focusPrimOp :: RST.PrimitiveOp -> [PrdCnsTerm] -> [PrdCnsTerm] -> Command
focusPrimOp op [] pcterms' = PrimOp defaultLoc op (MkSubstitution $ reverse pcterms')
focusPrimOp op (PrdTerm (isValueTerm PrdRep -> Just prd):pcterms) pcterms' = focusPrimOp op pcterms (PrdTerm prd : pcterms')
focusPrimOp op (PrdTerm prd:pcterms) pcterms' =
    let
        var = betaVar (length pcterms')
        cmd = LN.close [(Prd,var)]  (LN.shift ShiftUp (focusPrimOp op pcterms (PrdTerm (FreeVar defaultLoc PrdRep (getTypeTerm prd) var) : pcterms')))
    in
        Apply defaultLoc ApplyAnnotOrig (getKind (getTypeTerm prd)) (focus prd) (MuAbs defaultLoc MuAnnotOrig CnsRep (TyFlipPol NegRep (getTypeTerm prd)) Nothing cmd)
focusPrimOp op (CnsTerm (isValueTerm CnsRep -> Just cns):pcterms) pcterms' = focusPrimOp op pcterms (CnsTerm cns : pcterms')
focusPrimOp op (CnsTerm cns:pcterms) pcterms' =
    let
        var = betaVar (length pcterms')
        cmd = LN.close [(Cns,var)] (LN.shift ShiftUp (focusPrimOp op pcterms (CnsTerm (FreeVar defaultLoc CnsRep (getTypeTerm cns) var) : pcterms')))
    in
        Apply defaultLoc ApplyAnnotOrig (getKind (getTypeTerm cns)) (MuAbs defaultLoc MuAnnotOrig PrdRep (TyFlipPol PosRep (getTypeTerm cns)) Nothing cmd) (focus cns)

-- | Invariant:
-- The output should have the property `isFocusedCmd cmd`.
instance Focus Command where
  focus :: Command -> Command
  focus (Apply loc annot kind prd cns) = Apply loc annot kind (focus prd) (focus cns)
  focus (ExitSuccess loc) = ExitSuccess loc
  focus (ExitFailure loc) = ExitFailure loc
  focus (Jump loc fv) = Jump loc fv
  focus (Method loc mn cn subst) = Method loc mn cn (focus <¢> subst)
  -- Print
  focus (Print loc (isValueTerm PrdRep -> Just prd) cmd) =
    Print loc prd (focus cmd)
  focus (Print loc prd cmd) =
    let
      knd = getKind (getTypeTerm prd)
    in
      Apply loc ApplyAnnotOrig knd (focus prd)
                  (MuAbs loc MuAnnotOrig CnsRep (TyFlipPol NegRep (getTypeTerm prd)) Nothing (Print loc (BoundVar loc PrdRep (getTypeTerm prd) (0,0)) (focus cmd)))
  -- Read
  focus (Read loc (isValueTerm CnsRep -> Just cns)) =
    Read loc cns
  focus (Read loc cns) = 
    let
      knd = getKind (getTypeTerm cns)
    in
      Apply loc ApplyAnnotOrig knd (MuAbs loc MuAnnotOrig PrdRep (TyFlipPol PosRep (getTypeTerm cns)) Nothing (Read loc (BoundVar loc CnsRep (getTypeTerm cns) (0,0)))) (focus cns)
  focus (PrimOp _ op subst) = focusPrimOp op (unSubstitution subst) []

  isFocused :: Command -> Maybe Command
  isFocused (Apply loc _annot kind prd cns) = Apply loc ApplyAnnotOrig kind <$> isFocused prd <*> isFocused cns
  isFocused (ExitSuccess loc)              = Just (ExitSuccess loc)
  isFocused (ExitFailure loc)              = Just (ExitFailure loc)
  isFocused (Jump loc fv)                  = Just (Jump loc fv)
  isFocused (Method loc mn cn subst)       = Method loc mn cn <$> isFocused subst
  isFocused (Print loc prd cmd)            = Print loc <$> isValueTerm PrdRep prd <*> isFocused cmd
  isFocused (Read loc cns)                 = Read loc <$> isValueTerm CnsRep cns
  isFocused (PrimOp loc op subst)          = PrimOp loc op <$> isValueSubst subst

---------------------------------------------------------------------------------
-- Lift Focusing to programs
---------------------------------------------------------------------------------

instance Focus (PrdCnsDeclaration pc) where
  focus :: PrdCnsDeclaration pc -> PrdCnsDeclaration pc
  focus MkPrdCnsDeclaration { pcdecl_loc, pcdecl_doc, pcdecl_pc, pcdecl_isRec, pcdecl_name, pcdecl_annot, pcdecl_term } =
    MkPrdCnsDeclaration { pcdecl_loc = pcdecl_loc
                        , pcdecl_doc = pcdecl_doc
                        , pcdecl_pc = pcdecl_pc
                        , pcdecl_isRec = pcdecl_isRec
                        , pcdecl_name = pcdecl_name
                        , pcdecl_annot = pcdecl_annot
                        , pcdecl_term = focus pcdecl_term
                        }

  isFocused :: PrdCnsDeclaration pc -> Maybe (PrdCnsDeclaration pc)
  isFocused (MkPrdCnsDeclaration loc doc pc isrec fv annot tm) =
    MkPrdCnsDeclaration loc doc pc isrec fv annot <$> isFocused tm

instance Focus CommandDeclaration where
  focus :: CommandDeclaration -> CommandDeclaration
  focus MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd } =
    MkCommandDeclaration { cmddecl_loc = cmddecl_loc
                         , cmddecl_doc = cmddecl_doc
                         , cmddecl_name = cmddecl_name
                         , cmddecl_cmd = focus cmddecl_cmd
                         }
  
  isFocused :: CommandDeclaration -> Maybe CommandDeclaration
  isFocused (MkCommandDeclaration loc doc name cmd) =
    MkCommandDeclaration loc doc name <$> isFocused cmd

instance Focus InstanceDeclaration where
  focus :: InstanceDeclaration -> InstanceDeclaration
  focus MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_name, instancedecl_class, instancedecl_typ, instancedecl_cases } =
    MkInstanceDeclaration { instancedecl_loc
                          , instancedecl_doc
                          , instancedecl_name
                          , instancedecl_class
                          , instancedecl_typ
                          , instancedecl_cases = focus <$> instancedecl_cases
                          }
  
  isFocused :: InstanceDeclaration -> Maybe InstanceDeclaration
  isFocused (MkInstanceDeclaration loc doc name iclass typ cases) =
    MkInstanceDeclaration loc doc name iclass typ <$> mapM isFocused cases

instance Focus Declaration where
  focus :: Declaration -> Declaration
  focus (PrdCnsDecl pcrep decl) = PrdCnsDecl pcrep (focus decl)
  focus (CmdDecl decl)          = CmdDecl (focus decl)
  focus decl@DataDecl {}        = decl
  focus decl@XtorDecl {}        = decl
  focus decl@ImportDecl {}      = decl
  focus decl@SetDecl {}         = decl
  focus decl@TyOpDecl {}        = decl
  focus decl@TySynDecl {}       = decl
  focus decl@ClassDecl {}       = decl
  focus (InstanceDecl decl)     = InstanceDecl (focus decl)

  isFocused :: Declaration -> Maybe Declaration
  isFocused (PrdCnsDecl pcrep decl ) = PrdCnsDecl pcrep <$> isFocused decl
  isFocused (CmdDecl decl)           = CmdDecl <$> isFocused decl
  isFocused decl@DataDecl {}         = Just decl
  isFocused decl@XtorDecl {}         = Just decl
  isFocused decl@ImportDecl {}       = Just decl
  isFocused decl@SetDecl {}          = Just decl
  isFocused decl@TyOpDecl {}         = Just decl
  isFocused decl@TySynDecl {}        = Just decl
  isFocused decl@ClassDecl {}        = Just decl
  isFocused (InstanceDecl decl)      = InstanceDecl <$> isFocused decl

instance Focus Module where
  focus :: Module -> Module
  focus mod@MkModule { mod_decls } =
      mod { mod_decls = focus <$> mod_decls }
  
  isFocused :: Module -> Maybe Module
  isFocused mod@MkModule { mod_decls } =
    if any isNothing (isFocused <$> mod_decls)
    then Nothing
    else Just mod

instance Focus EvalEnv where
  focus :: EvalEnv -> EvalEnv
  focus (prd, cns, cmd) = (prd', cns', cmd')
    where
        prd' = focus <$> prd
        cns' = focus <$> cns
        cmd' = focus <$> cmd

  isFocused :: EvalEnv -> Maybe EvalEnv
  isFocused (prd,cns,cmd) = do
    prd' <- mapM isFocused prd
    cns' <- mapM isFocused cns
    cmd' <- mapM isFocused cmd
    pure (prd',cns',cmd')
