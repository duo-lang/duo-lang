module Resolution.Unresolve ( Unresolve(..), runUnresolveM ) where

import Control.Monad.State
import Data.Bifunctor
import Data.Text qualified as T
import Data.Maybe (fromJust)
import Data.List.NonEmpty (NonEmpty((:|)))

import Syntax.CST.Program qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
import Syntax.CST.Terms qualified as CST
import Syntax.RST.Program qualified as RST
import Syntax.RST.Types qualified as RST
import Syntax.RST.Terms qualified as RST
import Loc
import Syntax.RST.Terms (CmdCase(cmdcase_pat))
import Syntax.CST.Names
import qualified Syntax.LocallyNameless as LN

---------------------------------------------------------------------------------
-- The Unresolve Monad
---------------------------------------------------------------------------------

newtype UnresolveM a =
  MkUnresolveM { unUnresolveM :: State ([FreeVarName],[FreeVarName]) a }
    deriving newtype (Functor, Applicative,Monad, MonadState ([FreeVarName],[FreeVarName]))

runUnresolveM :: UnresolveM a -> a
runUnresolveM m = evalState (unUnresolveM m) names
  where
    names :: ([FreeVarName], [FreeVarName])
    names =  ((\y -> MkFreeVarName ("x" <> T.pack (show y))) <$> [(1 :: Int)..]
             ,(\y -> MkFreeVarName ("k" <> T.pack (show y))) <$> [(1 :: Int)..])

fresh :: PrdCns -> UnresolveM FreeVarName
fresh Prd = do
  var <- gets (head . fst)
  modify (first tail)
  pure var
fresh Cns = do
  var  <- gets (head . snd)
  modify (second tail)
  pure var

patternToSubst :: RST.Pattern -> RST.Substitution
patternToSubst (RST.XtorPat _loc _xt bs) = RST.MkSubstitution (f <$> bs)
  where
    f (Prd, Nothing) = error "Create Names first!"
    f (Prd, Just fv) = RST.PrdTerm $ RST.FreeVar defaultLoc PrdRep fv
    f (Cns, Nothing) = error "Create Names first!"
    f (Cns, Just fv) = RST.CnsTerm $ RST.FreeVar defaultLoc CnsRep fv

patternIToSubst :: RST.PatternI -> RST.Substitution
patternIToSubst (RST.XtorPatI _loc _xt (as1,(),as2)) = RST.MkSubstitution (f <$> (as1 <> [(Cns, Nothing)] <> as2))
  where
    f (Prd, Nothing) = error "Create Names first!"
    f (Prd, Just fv) = RST.PrdTerm $ RST.FreeVar defaultLoc PrdRep fv
    f (Cns, Nothing) = error "Create Names first!"
    f (Cns, Just fv) = RST.CnsTerm $ RST.FreeVar defaultLoc CnsRep fv

---------------------------------------------------------------------------------
-- helperfunctions
---------------------------------------------------------------------------------

isNumSTermRST :: RST.Term pc -> Maybe Int
isNumSTermRST (RST.Xtor _ PrdRep CST.Nominal (MkXtorName "Z") (RST.MkSubstitution [])) = Just 0
isNumSTermRST (RST.Xtor _ PrdRep CST.Nominal (MkXtorName "S") (RST.MkSubstitution [RST.PrdTerm n])) = case isNumSTermRST n of
  Nothing -> Nothing
  Just n -> Just (n + 1)
isNumSTermRST _ = Nothing

instance Unresolve RST.PrimitiveOp PrimName where
  unresolve :: RST.PrimitiveOp -> UnresolveM PrimName
  unresolve RST.I64Add = pure i64AddName
  unresolve RST.I64Sub = pure i64SubName
  unresolve RST.I64Mul = pure i64MulName
  unresolve RST.I64Div = pure i64DivName
  unresolve RST.I64Mod = pure i64ModName
  unresolve RST.F64Add = pure f64AddName
  unresolve RST.F64Sub = pure f64SubName
  unresolve RST.F64Mul = pure f64MulName
  unresolve RST.F64Div = pure f64DivName
  unresolve RST.CharPrepend = pure charPrependName
  unresolve RST.StringAppend = pure stringAppendName

---------------------------------------------------------------------------------
-- Unresolving
---------------------------------------------------------------------------------

class Open a where
  open :: a -> UnresolveM a

class EmbedRST a b | a -> b where
  embedRST :: a -> UnresolveM b

class Unresolve a b | a -> b where
  unresolve :: a -> UnresolveM b

---------------------------------------------------------------------------------
-- Unresolving terms
---------------------------------------------------------------------------------

-- PrdCnsTerm

instance Open RST.PrdCnsTerm where
  open :: RST.PrdCnsTerm -> UnresolveM RST.PrdCnsTerm
  open (RST.PrdTerm tm) = RST.PrdTerm <$> open tm
  open (RST.CnsTerm tm) = RST.CnsTerm <$> open tm

instance EmbedRST RST.PrdCnsTerm CST.Term where
  embedRST :: RST.PrdCnsTerm -> UnresolveM CST.Term
  embedRST (RST.PrdTerm tm) = embedRST tm
  embedRST (RST.CnsTerm tm) = embedRST tm

instance Unresolve RST.PrdCnsTerm CST.Term where
  unresolve :: RST.PrdCnsTerm -> UnresolveM CST.Term
  unresolve (RST.PrdTerm tm) = unresolve tm
  unresolve (RST.CnsTerm tm) = unresolve tm

-- Substitution

instance Open RST.Substitution where
  open :: RST.Substitution -> UnresolveM RST.Substitution
  open (RST.MkSubstitution subst) = do
    subst' <- mapM open subst
    pure $ RST.MkSubstitution subst'

instance EmbedRST RST.Substitution CST.Substitution where
  embedRST :: RST.Substitution -> UnresolveM CST.Substitution
  embedRST (RST.MkSubstitution subst) = do
    subst' <- mapM embedRST subst
    pure $ CST.MkSubstitution subst'

instance Unresolve RST.Substitution CST.Substitution where
  unresolve :: RST.Substitution -> UnresolveM CST.Substitution
  unresolve (RST.MkSubstitution subst) = do
    subst' <- mapM unresolve subst
    pure (CST.MkSubstitution subst')

-- SubstitutionI

instance Open (RST.SubstitutionI pc) where
  open :: RST.SubstitutionI pc -> UnresolveM (RST.SubstitutionI pc)
  open (RST.MkSubstitutionI (subst1,pc,subst2)) = do
    subst1' <- mapM open subst1
    subst2' <- mapM open subst2
    pure $ RST.MkSubstitutionI (subst1',pc,subst2')

instance EmbedRST (RST.SubstitutionI pc) CST.SubstitutionI where
  embedRST :: RST.SubstitutionI pc -> UnresolveM CST.SubstitutionI
  embedRST (RST.MkSubstitutionI (subst1,_,subst2)) = do
    subst1' <- mapM (fmap CST.ToSTerm . embedRST) subst1
    subst2' <- mapM (fmap CST.ToSTerm . embedRST) subst2
    pure $ CST.MkSubstitutionI (subst1' <> [CST.ToSStar] <> subst2')

instance Unresolve (RST.SubstitutionI pc) CST.SubstitutionI where
  unresolve :: RST.SubstitutionI pc -> UnresolveM CST.SubstitutionI
  unresolve (RST.MkSubstitutionI (subst1,_,subst2)) = do
    subst1' <- mapM (fmap CST.ToSTerm . unresolve) subst1
    subst2' <- mapM (fmap CST.ToSTerm . unresolve) subst2
    pure $ CST.MkSubstitutionI (subst1' <> [CST.ToSStar] <> subst2')

-- Pattern

instance Open RST.Pattern where
  open :: RST.Pattern -> UnresolveM RST.Pattern
  open (RST.XtorPat loc xt args) = do
    args' <- mapM (\(pc,_) -> fresh pc >>= \v -> return (pc, Just v)) args
    pure $ RST.XtorPat loc xt args'

instance EmbedRST RST.Pattern CST.Pattern where
  embedRST :: RST.Pattern -> UnresolveM CST.Pattern
  embedRST (RST.XtorPat loc xt args) =
    pure $ CST.PatXtor loc xt (CST.PatVar loc . fromJust . snd <$> args)

-- PatternI

instance Open RST.PatternI where
  open :: RST.PatternI -> UnresolveM RST.PatternI
  open (RST.XtorPatI loc xt (as1, (), as2)) = do
    let f (pc,_) = fresh pc >>= \v -> return (pc, Just v)
    as1' <- mapM f as1
    as2' <- mapM f as2
    pure $ RST.XtorPatI loc xt (as1', (), as2')

instance EmbedRST RST.PatternI CST.Pattern where
  embedRST :: RST.PatternI -> UnresolveM CST.Pattern
  embedRST (RST.XtorPatI loc xt (as1,_,as2)) =
    pure $ CST.PatXtor loc xt ((CST.PatVar loc . fromJust . snd <$> as1) ++ [CST.PatStar loc] ++ (CST.PatVar loc . fromJust . snd  <$> as2))

-- CmdCase

instance Open RST.CmdCase where
  open :: RST.CmdCase -> UnresolveM RST.CmdCase
  open RST.MkCmdCase { cmdcase_loc, cmdcase_pat, cmdcase_cmd } = do
    pat' <- open cmdcase_pat
    cmd' <- open cmdcase_cmd
    let cmd'' = LN.open (patternToSubst pat') cmd'
    pure RST.MkCmdCase { cmdcase_loc = cmdcase_loc
                       , cmdcase_pat = pat'
                       , cmdcase_cmd = cmd''
                       }

instance EmbedRST RST.CmdCase CST.TermCase where
  embedRST :: RST.CmdCase -> UnresolveM CST.TermCase
  embedRST RST.MkCmdCase { cmdcase_loc, cmdcase_pat, cmdcase_cmd } = do
    pat' <- embedRST cmdcase_pat
    cmd' <- embedRST cmdcase_cmd
    pure $ CST.MkTermCase { tmcase_loc = cmdcase_loc
                          , tmcase_pat = pat'
                          , tmcase_term = cmd'
                          }

instance Unresolve RST.CmdCase CST.TermCase where
  unresolve :: RST.CmdCase -> UnresolveM CST.TermCase
  unresolve cmdcase = embedRST (runUnresolveM (open cmdcase))

-- TermCase

instance Open (RST.TermCase pc) where
  open :: RST.TermCase pc -> UnresolveM (RST.TermCase pc)
  open RST.MkTermCase { tmcase_loc, tmcase_pat, tmcase_term } = do
    pat' <- open tmcase_pat
    term' <- open tmcase_term
    let term'' = LN.open (patternToSubst pat') term'
    pure RST.MkTermCase { tmcase_loc = tmcase_loc
                        , tmcase_pat = pat'
                        , tmcase_term = term''
                        }

instance EmbedRST (RST.TermCase pc) CST.TermCase where
  embedRST :: RST.TermCase pc -> UnresolveM CST.TermCase
  embedRST RST.MkTermCase { tmcase_loc, tmcase_pat, tmcase_term } = do
    pat <- embedRST tmcase_pat
    term <- embedRST tmcase_term
    pure $ CST.MkTermCase { tmcase_loc = tmcase_loc
                          , tmcase_pat = pat
                          , tmcase_term = term
                          }

instance Unresolve (RST.TermCase pc) CST.TermCase where
  unresolve :: RST.TermCase pc -> UnresolveM CST.TermCase
  unresolve termcase = embedRST (runUnresolveM (open termcase))

-- TermCaseI

instance Open (RST.TermCaseI pc) where
  open :: RST.TermCaseI pc -> UnresolveM (RST.TermCaseI pc)
  open RST.MkTermCaseI { tmcasei_loc, tmcasei_pat, tmcasei_term } = do
    pat' <- open tmcasei_pat
    term' <- open tmcasei_term
    let term'' = LN.open (patternIToSubst pat') term'
    pure RST.MkTermCaseI { tmcasei_loc = tmcasei_loc
                         , tmcasei_pat = pat'
                         , tmcasei_term = term''
                         }

instance EmbedRST (RST.TermCaseI pc) CST.TermCase where
  embedRST :: RST.TermCaseI pc -> UnresolveM CST.TermCase
  embedRST RST.MkTermCaseI { tmcasei_loc, tmcasei_pat, tmcasei_term } = do
    pat <- embedRST tmcasei_pat
    term <- embedRST tmcasei_term
    pure CST.MkTermCase { tmcase_loc = tmcasei_loc
                        , tmcase_pat = pat
                        , tmcase_term = term
                        }

instance Unresolve (RST.TermCaseI pc) CST.TermCase where
  unresolve :: RST.TermCaseI pc -> UnresolveM CST.TermCase
  unresolve termcasei = embedRST (runUnresolveM (open termcasei))

-- InstanceCase

instance Open RST.InstanceCase where
  open :: RST.InstanceCase -> UnresolveM RST.InstanceCase
  open RST.MkInstanceCase { instancecase_loc, instancecase_pat, instancecase_cmd } = do
    pat <- open instancecase_pat
    cmd' <- open instancecase_cmd
    let cmd'' = LN.open (patternToSubst pat) cmd'
    pure RST.MkInstanceCase { instancecase_loc = instancecase_loc
                            , instancecase_pat = pat
                            , instancecase_cmd = cmd''
                            }

instance EmbedRST RST.InstanceCase CST.TermCase where
  embedRST :: RST.InstanceCase -> UnresolveM CST.TermCase
  embedRST RST.MkInstanceCase { instancecase_loc, instancecase_pat, instancecase_cmd } = do
    pat <- embedRST instancecase_pat
    cmd <- embedRST instancecase_cmd
    pure CST.MkTermCase { tmcase_loc = instancecase_loc
                        , tmcase_pat = pat
                        , tmcase_term = cmd
                        }

instance Unresolve RST.InstanceCase CST.TermCase where
  unresolve :: RST.InstanceCase -> UnresolveM CST.TermCase
  unresolve = open >=> embedRST

-- Term

instance Open (RST.Term pc) where
  open :: RST.Term pc -> UnresolveM (RST.Term pc)
  -- Core constructs
  open (RST.BoundVar loc pc idx) =
    pure $ RST.BoundVar loc pc idx
  open (RST.FreeVar loc pc v) =
    pure $ RST.FreeVar loc pc v
  open (RST.Xtor loc pc ns xt args) = do
    args' <- open args
    pure $ RST.Xtor loc pc ns xt args'
  open (RST.XCase loc pc ns cases) = do
    cases' <- mapM open cases
    pure $ RST.XCase loc pc ns cases'
  open (RST.MuAbs loc pc _ cmd) = do
    fv <- fresh (case pc of PrdRep -> Cns; CnsRep -> Prd)
    cmd' <- open cmd
    let cmd'' = case pc of
                PrdRep -> LN.open (RST.MkSubstitution [RST.CnsTerm (RST.FreeVar defaultLoc CnsRep fv)]) cmd'
                CnsRep -> LN.open (RST.MkSubstitution [RST.PrdTerm (RST.FreeVar defaultLoc PrdRep fv)]) cmd'
    pure $ RST.MuAbs loc pc (Just fv) cmd''
  -- Syntactic sugar
  open (RST.Semi loc rep ns xt subst t) = do
    subst' <- open subst
    t' <- open t
    pure $ RST.Semi loc rep ns xt subst' t'
  open (RST.Dtor loc rep ns xt t subst) = do
    t' <- open t
    subst' <- open subst
    pure $ RST.Dtor loc rep ns xt t' subst'
  open (RST.CaseOf loc rep ns t cases) = do
    t' <- open t
    cases' <- mapM open cases
    pure $ RST.CaseOf loc rep ns t' cases'
  open (RST.CocaseOf loc rep ns t cases) = do
    t' <- open t
    cases' <- mapM open cases
    pure $ RST.CocaseOf loc rep ns t' cases'
  open (RST.CaseI loc rep ns cases) = do
    cases' <- mapM open cases
    pure $ RST.CaseI loc rep ns cases'
  open (RST.CocaseI loc rep ns cocases) = do
    cocases' <- mapM open cocases
    pure $ RST.CocaseI loc rep ns cocases'
  open (RST.Lambda loc pc fv tm) = do
    tm' <- open tm
    let tm'' = case pc of PrdRep -> LN.open (RST.MkSubstitution [RST.PrdTerm (RST.FreeVar defaultLoc PrdRep fv)]) tm'
                          CnsRep -> LN.open (RST.MkSubstitution [RST.CnsTerm (RST.FreeVar defaultLoc CnsRep fv)]) tm'
    pure $ RST.Lambda loc pc fv tm''
  -- Primitive constructs
  open (RST.PrimLitI64 loc i) =
    pure $ RST.PrimLitI64 loc i
  open (RST.PrimLitF64 loc d) =
    pure $ RST.PrimLitF64 loc d
  open (RST.PrimLitChar loc d) =
    pure $ RST.PrimLitChar loc d
  open (RST.PrimLitString loc d) =
    pure $ RST.PrimLitString loc d
  
instance EmbedRST (RST.Term pc) CST.Term where
  embedRST :: RST.Term pc -> UnresolveM CST.Term
  embedRST (isNumSTermRST -> Just i) =
    pure $ CST.NatLit defaultLoc CST.Nominal i
  -- Core constructs
  embedRST RST.BoundVar{} =
    error "Should have been removed by opening"
  embedRST (RST.FreeVar loc _ fv) =
    pure $ CST.Var loc fv
  embedRST (RST.Xtor loc _ _ xt (RST.MkSubstitution subst)) = do
    subst' <- mapM (fmap CST.ToSTerm . embedRST) subst
    pure $ CST.Xtor loc xt (CST.MkSubstitutionI subst')
  embedRST (RST.XCase loc PrdRep _ cases) = do
    cases' <- mapM embedRST cases
    pure $ CST.Cocase loc cases'
  embedRST (RST.XCase loc CnsRep _ cases) = do
    cases' <- mapM embedRST cases
    pure $ CST.Case loc cases'
  embedRST (RST.MuAbs loc _ fv cmd) = do
    cmd' <- embedRST cmd
    pure $ CST.MuAbs loc (fromJust fv) cmd'
  -- Syntactic sugar
  embedRST (RST.Semi loc _ _ (MkXtorName "CoAp") (RST.MkSubstitutionI ([RST.CnsTerm t],CnsRep,[])) tm) = do
    tm' <- embedRST tm
    t' <- embedRST t
    pure $ CST.FunApp loc tm' t'
  embedRST (RST.Semi _loc _ _ (MkXtorName "CoAp")  other _tm) =
    error $ "embed: " ++ show  other
  embedRST (RST.Semi loc _ _ xt substi tm) = do
    substi' <- embedRST substi
    tm' <- embedRST tm
    pure $ CST.Semi loc xt substi' tm'
  embedRST (RST.Dtor loc _ _ (MkXtorName "Ap") tm (RST.MkSubstitutionI ([RST.PrdTerm t],PrdRep,[]))) = do
    tm' <- embedRST tm
    t' <- embedRST t
    pure $ CST.FunApp loc tm' t'
  embedRST (RST.Dtor loc _ _ xt tm substi) = do
    tm' <- embedRST tm
    substi' <- embedRST substi
    pure $ CST.Dtor loc xt tm' substi'
  embedRST (RST.CaseOf loc _ _ tm cases) = do
    tm' <- embedRST tm
    cases' <- mapM embedRST cases
    pure $ CST.CaseOf loc tm' cases'
  embedRST (RST.CocaseOf loc _ _ tm cases) = do
    tm' <- embedRST tm
    cases' <- mapM embedRST cases
    pure $ CST.CocaseOf loc tm' cases'
  embedRST (RST.CaseI loc _ _ cases) = do
    cases' <- mapM embedRST cases
    pure $ CST.Case loc cases'
  embedRST (RST.CocaseI loc _ _ cases) = do
    cases' <- mapM embedRST cases
    pure $ CST.Cocase loc cases'
  embedRST (RST.Lambda loc PrdRep fvs tm) = do
    tm' <- embedRST tm
    pure $ CST.Lambda loc fvs tm'
  embedRST (RST.Lambda loc CnsRep fvs tm) = do
    tm' <- embedRST tm
    pure $ CST.CoLambda loc fvs tm'
  embedRST (RST.PrimLitI64 loc i) =
    pure $ CST.PrimLitI64 loc i
  embedRST (RST.PrimLitF64 loc d) =
    pure $ CST.PrimLitF64 loc d
  embedRST (RST.PrimLitChar loc d) =
    pure $ CST.PrimLitChar loc d
  embedRST (RST.PrimLitString loc d) =
    pure $ CST.PrimLitString loc d

instance Unresolve (RST.Term pc) CST.Term where
  unresolve :: RST.Term pc -> UnresolveM CST.Term
  unresolve = open >=> embedRST

-- Command

instance Open RST.Command where
  open :: RST.Command -> UnresolveM RST.Command
  open (RST.Apply loc t1 t2) = do
    t1' <- open t1
    t2' <- open t2
    pure $ RST.Apply loc t1' t2'
  open (RST.Print loc t cmd) = do
    t' <- open t
    cmd' <- open cmd
    pure $ RST.Print loc t' cmd'
  open (RST.Read loc cns) = do
    cns' <- open cns
    pure $ RST.Read loc cns'
  open (RST.Jump loc fv) =
    pure $ RST.Jump loc fv
  open (RST.Method loc mn cn subst) = do
    subst' <- open subst
    pure $ RST.Method loc mn cn subst'
  open (RST.ExitSuccess loc) =
    pure $ RST.ExitSuccess loc
  open (RST.ExitFailure loc) =
    pure $ RST.ExitFailure loc
  open (RST.PrimOp loc op subst) = do
    subst' <- open subst
    pure $ RST.PrimOp loc op subst'
  open (RST.CaseOfCmd loc ns tm cases) = do
    tm' <- open tm
    cases' <- mapM open cases
    pure $ RST.CaseOfCmd loc ns tm' cases'
  open (RST.CocaseOfCmd loc ns tm cases) = do
    tm' <- open tm
    cases' <- mapM open cases
    pure $ RST.CocaseOfCmd loc ns tm' cases'
  open (RST.CaseOfI loc rep ns tm cases) = do
    tm' <- open tm
    cases' <- mapM open cases
    pure $ RST.CaseOfI loc rep ns tm' cases'
  open (RST.CocaseOfI loc rep ns tm cases) = do
    tm' <- open tm
    cases' <- mapM open cases
    pure $ RST.CocaseOfI loc rep ns tm' cases'

instance EmbedRST RST.Command CST.Term where
  embedRST :: RST.Command -> UnresolveM CST.Term
  embedRST (RST.Apply loc prd cns) = do
    prd' <- embedRST prd
    cns' <- embedRST cns
    pure $ CST.Apply loc prd' cns'
  embedRST (RST.Print loc tm cmd) = do
    tm' <- embedRST tm
    cmd' <- embedRST cmd
    pure $ CST.PrimTerm loc printName (CST.MkSubstitution [tm', cmd'])
  embedRST (RST.Read loc cns) = do
    cns' <- embedRST cns
    pure $ CST.PrimTerm loc readName (CST.MkSubstitution [cns'])
  embedRST (RST.Jump loc fv) =
    pure $ CST.Var loc fv
  embedRST (RST.Method loc mn _cn (RST.MkSubstitution subst)) = do
    subst' <- mapM (fmap CST.ToSTerm . embedRST) subst
    pure $ CST.Xtor loc (MkXtorName $ unMethodName mn) (CST.MkSubstitutionI subst')
  embedRST (RST.ExitSuccess loc) =
    pure $ CST.PrimTerm loc exitSuccessName (CST.MkSubstitution [])
  embedRST (RST.ExitFailure loc) =
    pure $ CST.PrimTerm loc exitFailureName (CST.MkSubstitution [])
  embedRST (RST.PrimOp loc op subst) = do
    op' <- unresolve op
    subst' <- embedRST subst
    pure $ CST.PrimTerm loc op' subst'
  embedRST (RST.CaseOfCmd loc _ns tm cases) = do
    tm' <- embedRST tm
    cases' <- mapM embedRST cases
    pure $ CST.CaseOf loc tm' cases'
  embedRST (RST.CocaseOfCmd loc _ns tm cases) = do
    tm' <- embedRST tm
    cases' <- mapM embedRST cases
    pure $ CST.CocaseOf loc tm' cases'
  embedRST (RST.CaseOfI loc _rep _ns tm cases) = do
    tm' <- embedRST tm
    cases' <- mapM embedRST cases
    pure $ CST.CaseOf loc tm' cases'
  embedRST (RST.CocaseOfI loc _rep _ns tm cases) = do
    tm' <- embedRST tm
    cases' <- mapM embedRST cases
    pure $ CST.CocaseOf loc tm' cases'

instance Unresolve RST.Command CST.Term where
  unresolve :: RST.Command -> UnresolveM CST.Term
  unresolve = open >=> embedRST 

---------------------------------------------------------------------------------
-- Unresolving types
---------------------------------------------------------------------------------

instance Unresolve (RST.PrdCnsType pol) CST.PrdCnsTyp where
  unresolve :: RST.PrdCnsType pol -> UnresolveM CST.PrdCnsTyp
  unresolve (RST.PrdCnsType PrdRep ty) = CST.PrdType <$> unresolve ty
  unresolve (RST.PrdCnsType CnsRep ty) = CST.CnsType <$> unresolve ty

instance Unresolve (RST.LinearContext pol) CST.LinearContext where
  unresolve :: RST.LinearContext pol -> UnresolveM CST.LinearContext
  unresolve = mapM unresolve

instance Unresolve (RST.XtorSig pol) CST.XtorSig where
  unresolve :: RST.XtorSig pol -> UnresolveM CST.XtorSig
  unresolve RST.MkXtorSig { sig_name, sig_args } = do
    sig_args' <- unresolve sig_args
    pure CST.MkXtorSig { sig_name = sig_name
                       , sig_args = sig_args'
                       }

instance Unresolve (RST.VariantType pol) CST.Typ where
  unresolve :: RST.VariantType pol -> UnresolveM CST.Typ
  unresolve (RST.CovariantType ty) = unresolve ty
  unresolve (RST.ContravariantType ty) = unresolve ty

resugarType :: RST.Typ pol -> UnresolveM (Maybe CST.Typ)
resugarType (RST.TyNominal loc _ MkRnTypeName { rnTnName = MkTypeName "Fun" } [RST.ContravariantType tl, RST.CovariantType tr]) = do
  tl' <- unresolve tl
  tr' <- unresolve tr
  pure $ Just (CST.TyBinOp loc tl' (CustomOp (MkTyOpName "->")) tr')
resugarType (RST.TyNominal loc _ MkRnTypeName { rnTnName = MkTypeName "CoFun" } [RST.CovariantType tl, RST.ContravariantType tr]) = do
  tl' <- unresolve tl
  tr' <- unresolve tr
  pure $ Just (CST.TyBinOp loc tl' (CustomOp (MkTyOpName "-<")) tr')
resugarType (RST.TyNominal loc _ MkRnTypeName { rnTnName = MkTypeName "Par" } [RST.CovariantType tl, RST.CovariantType tr]) = do
  tl' <- unresolve tl
  tr' <- unresolve tr
  pure $ Just (CST.TyBinOp loc tl' (CustomOp (MkTyOpName "⅋")) tr')
resugarType _ = pure Nothing

embedRecTVar :: RecTVar -> SkolemTVar
embedRecTVar (MkRecTVar n) = MkSkolemTVar n

instance Unresolve (RST.Typ pol) CST.Typ where
  unresolve :: RST.Typ pol -> UnresolveM CST.Typ
  unresolve (runUnresolveM . resugarType -> Just ty) = pure ty
  unresolve (RST.TyUniVar loc _ tv) =
    pure $ CST.TyUniVar loc tv
  unresolve (RST.TySkolemVar loc _ tv) =
    pure $ CST.TySkolemVar loc tv
  unresolve (RST.TyRecVar loc _ tv) =
    pure $ CST.TySkolemVar loc $ embedRecTVar tv
  unresolve (RST.TyData loc _ xtors) = do
    xtors' <- mapM unresolve xtors
    pure $ CST.TyXData loc CST.Data xtors'
  unresolve (RST.TyCodata loc _ xtors) = do
    xtors' <- mapM unresolve xtors
    pure $ CST.TyXData loc CST.Codata xtors'
  unresolve (RST.TyDataRefined loc _ tn xtors) = do
    xtors' <- mapM unresolve xtors
    pure $ CST.TyXRefined loc CST.Data (rnTnName tn) xtors'
  unresolve (RST.TyCodataRefined loc _ tn xtors) = do
    xtors' <- mapM unresolve xtors
    pure $ CST.TyXRefined loc CST.Codata (rnTnName tn) xtors'
  unresolve (RST.TyNominal loc _ nm args) = do
    args' <- mapM unresolve args
    case args' of 
      [] -> pure $ CST.TyNominal loc (rnTnName nm)
      (fst:rst) -> pure $ CST.TyApp loc (CST.TyNominal loc (rnTnName nm)) (fst :| rst)
  unresolve (RST.TySyn loc _ nm _) =
    pure $ CST.TyNominal loc (rnTnName nm)
  unresolve (RST.TyTop loc) =
    pure $ CST.TyTop loc
  unresolve (RST.TyBot loc) =
    pure $ CST.TyBot loc
  unresolve (RST.TyUnion loc tyl tyr) = do
    tyl' <- unresolve tyl
    tyr' <- unresolve tyr
    pure $ CST.TyBinOp loc tyl' UnionOp tyr'
  unresolve (RST.TyInter loc tyl tyr) = do
    tyl' <- unresolve tyl
    tyr' <- unresolve tyr
    pure $ CST.TyBinOp loc tyl' InterOp tyr'
  unresolve (RST.TyRec loc _ tv ty) = do
    ty' <- unresolve ty
    pure $ CST.TyRec loc (embedRecTVar tv) ty'
  unresolve (RST.TyI64 loc _) =
    pure $ CST.TyI64 loc
  unresolve (RST.TyF64 loc _) =
    pure $ CST.TyF64 loc
  unresolve (RST.TyChar loc _) =
    pure $ CST.TyChar loc
  unresolve (RST.TyString loc _) =
    pure $ CST.TyString loc
  unresolve (RST.TyFlipPol _ ty) =
    unresolve ty
  unresolve (RST.TyKindAnnot mk ty) = do 
    ty' <- unresolve ty
    pure $ CST.TyKindAnnot mk ty'

instance Unresolve (RST.TypeScheme pol) CST.TypeScheme where
  unresolve :: RST.TypeScheme pol -> UnresolveM CST.TypeScheme
  unresolve RST.TypeScheme { ts_loc, ts_vars, ts_monotype } = do
    type' <- unresolve ts_monotype
    pure $ CST.TypeScheme  { ts_loc         = ts_loc
                           , ts_vars        = ts_vars
                           , ts_constraints = []
                           , ts_monotype    = type'
                           }

instance Unresolve (RST.MethodSig pol) CST.XtorSig where
  unresolve :: RST.MethodSig pol -> UnresolveM CST.XtorSig
  unresolve RST.MkMethodSig { msig_name, msig_args } = do
    args' <- mapM unresolve msig_args
    pure CST.MkXtorSig { sig_name = MkXtorName $ unMethodName msig_name
                       , sig_args = args'
                       }

---------------------------------------------------------------------------------
-- Unresolving declarations
---------------------------------------------------------------------------------

instance Unresolve (RST.PrdCnsDeclaration pc) CST.PrdCnsDeclaration where
  unresolve :: RST.PrdCnsDeclaration pc -> UnresolveM CST.PrdCnsDeclaration
  unresolve RST.MkPrdCnsDeclaration { pcdecl_loc, pcdecl_doc, pcdecl_pc, pcdecl_isRec, pcdecl_name, pcdecl_annot, pcdecl_term } = do
    annot' <- mapM unresolve pcdecl_annot
    term' <- unresolve pcdecl_term
    pure $ CST.MkPrdCnsDeclaration { pcdecl_loc   = pcdecl_loc
                                   , pcdecl_doc   = pcdecl_doc
                                   , pcdecl_pc    = case pcdecl_pc of { PrdRep -> Prd; CnsRep -> Cns }
                                   , pcdecl_isRec = pcdecl_isRec
                                   , pcdecl_name  = pcdecl_name
                                   , pcdecl_annot = annot'
                                   , pcdecl_term  = term'
                                   }

instance Unresolve RST.CommandDeclaration CST.CommandDeclaration where
  unresolve :: RST.CommandDeclaration -> UnresolveM CST.CommandDeclaration
  unresolve RST.MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd } = do
    cmd' <- unresolve cmddecl_cmd
    pure $ CST.MkCommandDeclaration  { cmddecl_loc  = cmddecl_loc
                                     , cmddecl_doc  = cmddecl_doc
                                     , cmddecl_name = cmddecl_name
                                     , cmddecl_cmd  = cmd'
                                     }

instance Unresolve RST.StructuralXtorDeclaration CST.StructuralXtorDeclaration where
  unresolve :: RST.StructuralXtorDeclaration -> UnresolveM CST.StructuralXtorDeclaration
  unresolve RST.MkStructuralXtorDeclaration { strxtordecl_loc, strxtordecl_doc, strxtordecl_xdata, strxtordecl_name, strxtordecl_arity, strxtordecl_evalOrder} =
    pure CST.MkStructuralXtorDeclaration { strxtordecl_loc       = strxtordecl_loc
                                         , strxtordecl_doc       = strxtordecl_doc
                                         , strxtordecl_xdata     = strxtordecl_xdata
                                         , strxtordecl_name      = strxtordecl_name
                                         , strxtordecl_arity     = strxtordecl_arity
                                         , strxtordecl_evalOrder = Just strxtordecl_evalOrder
                                         }

instance Unresolve RST.TySynDeclaration CST.TySynDeclaration where
  unresolve :: RST.TySynDeclaration -> UnresolveM CST.TySynDeclaration
  unresolve RST.MkTySynDeclaration { tysyndecl_loc, tysyndecl_doc, tysyndecl_name, tysyndecl_res } = do
    res' <- unresolve (fst tysyndecl_res)
    pure CST.MkTySynDeclaration  { tysyndecl_loc  = tysyndecl_loc
                                 , tysyndecl_doc  = tysyndecl_doc
                                 , tysyndecl_name = tysyndecl_name
                                 , tysyndecl_res  = res'
                                 }

instance Unresolve RST.TyOpDeclaration CST.TyOpDeclaration where
  unresolve :: RST.TyOpDeclaration -> UnresolveM CST.TyOpDeclaration
  unresolve RST.MkTyOpDeclaration { tyopdecl_loc, tyopdecl_doc, tyopdecl_sym, tyopdecl_prec, tyopdecl_assoc, tyopdecl_res } =
    pure CST.MkTyOpDeclaration { tyopdecl_loc   = tyopdecl_loc
                               , tyopdecl_doc   = tyopdecl_doc
                               , tyopdecl_sym   = tyopdecl_sym
                               , tyopdecl_prec  = tyopdecl_prec
                               , tyopdecl_assoc = tyopdecl_assoc
                               , tyopdecl_res   = rnTnName tyopdecl_res
                               }

instance Unresolve RST.ClassDeclaration CST.ClassDeclaration where
  unresolve :: RST.ClassDeclaration -> UnresolveM CST.ClassDeclaration
  unresolve RST.MkClassDeclaration { classdecl_loc, classdecl_doc, classdecl_name, classdecl_kinds, classdecl_methods } = do
    methods' <- mapM unresolve (fst classdecl_methods)
    pure $ CST.MkClassDeclaration  { classdecl_loc     = classdecl_loc
                                   , classdecl_doc     = classdecl_doc
                                   , classdecl_name    = classdecl_name
                                   , classdecl_kinds   = classdecl_kinds
                                   , classdecl_methods = methods'
                                   }

instance Unresolve RST.InstanceDeclaration CST.InstanceDeclaration where
  unresolve :: RST.InstanceDeclaration -> UnresolveM CST.InstanceDeclaration
  unresolve RST.MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_name, instancedecl_class, instancedecl_typ, instancedecl_cases } = do
    typ' <- unresolve (fst instancedecl_typ)
    cases' <- mapM unresolve instancedecl_cases
    pure $ CST.MkInstanceDeclaration { instancedecl_loc   = instancedecl_loc
                                     , instancedecl_doc   = instancedecl_doc
                                     , instancedecl_name  = instancedecl_name
                                     , instancedecl_class = instancedecl_class
                                     , instancedecl_typ   = typ'
                                     , instancedecl_cases = cases'
                                     }

instance Unresolve RST.DataDecl CST.DataDecl where
  unresolve :: RST.DataDecl -> UnresolveM CST.DataDecl
  unresolve RST.NominalDecl { data_loc, data_doc, data_name, data_polarity, data_kind, data_xtors } = do
    xtors' <- mapM unresolve (fst data_xtors)
    pure $ CST.MkDataDecl { data_loc      = data_loc
                          , data_doc      = data_doc
                          , data_refined  = CST.NotRefined
                          , data_name     = rnTnName data_name
                          , data_polarity = data_polarity
                          , data_kind     = Just data_kind
                          , data_xtors    = xtors'
                          }
  unresolve RST.RefinementDecl { data_loc, data_doc, data_name, data_polarity, data_kind, data_xtors } = do
    xtors' <- mapM unresolve (fst data_xtors)
    pure $ CST.MkDataDecl { data_loc      = data_loc
                          , data_doc      = data_doc
                          , data_refined  = CST.Refined
                          , data_name     = rnTnName data_name
                          , data_polarity = data_polarity
                          , data_kind     = Just data_kind
                          , data_xtors    = xtors'
                          }

instance Unresolve RST.Declaration CST.Declaration where
  unresolve :: RST.Declaration -> UnresolveM CST.Declaration
  unresolve (RST.PrdCnsDecl _ decl) =
    CST.PrdCnsDecl <$> unresolve decl
  unresolve (RST.CmdDecl decl) =
    CST.CmdDecl <$> unresolve decl
  unresolve (RST.DataDecl decl) =
    CST.DataDecl <$> unresolve decl
  unresolve (RST.XtorDecl decl) =
    CST.XtorDecl <$> unresolve decl
  unresolve (RST.ImportDecl decl) =
    pure $ CST.ImportDecl decl
  unresolve (RST.SetDecl decl) =
    pure $ CST.SetDecl decl
  unresolve (RST.TyOpDecl decl) =
    CST.TyOpDecl <$> unresolve decl
  unresolve (RST.TySynDecl decl) =
    CST.TySynDecl <$> unresolve decl
  unresolve (RST.ClassDecl decl) =
    CST.ClassDecl <$> unresolve decl
  unresolve (RST.InstanceDecl decl) =
    CST.InstanceDecl <$> unresolve decl

instance Unresolve RST.Module CST.Module where
  unresolve :: RST.Module -> UnresolveM CST.Module
  unresolve RST.MkModule { mod_name, mod_libpath, mod_decls } = do
    decls' <- mapM unresolve mod_decls
    pure $ CST.MkModule  { mod_name = mod_name
                         , mod_libpath = mod_libpath
                         , mod_decls = decls'
                         }
