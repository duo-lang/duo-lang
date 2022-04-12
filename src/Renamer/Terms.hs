module Renamer.Terms (renameTerm, renameCommand) where

import Control.Monad.Except (throwError)
import Data.Bifunctor ( second )
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map qualified as M
import Text.Megaparsec.Pos (SourcePos)

import Errors
import Renamer.Definition
import Syntax.RST.Terms qualified as RST
import Syntax.CST.Terms qualified as CST
import Syntax.Common
import Utils

---------------------------------------------------------------------------------
-- Check Arity of Xtor
---------------------------------------------------------------------------------

checkXtorArity :: Loc -> (XtorName, DataCodata) -> Arity -> RenamerM ()
checkXtorArity loc (xt, dc) arityUsed = do
  (_,(_,aritySpecified)) <- lookupXtor loc (xt, dc)
  if arityUsed /= aritySpecified
    then throwError (LowerError (Just loc) (XtorArityMismatch xt aritySpecified arityUsed))
    else pure ()


---------------------------------------------------------------------------------
-- Check Arity of Xtor
---------------------------------------------------------------------------------

renameSubstitution :: CST.Substitution -> RenamerM RST.Substitution
renameSubstitution [] = pure []
renameSubstitution (CST.PrdTerm tm:tms) = do
  tm' <- renameTerm PrdRep tm
  subst <- renameSubstitution tms
  pure (RST.PrdTerm tm':subst)
renameSubstitution (CST.CnsTerm tm:tms) = do
  tm' <- renameTerm CnsRep tm
  subst <- renameSubstitution tms
  pure (RST.CnsTerm tm':subst)


renameSubstitutionI :: CST.SubstitutionI -> RenamerM (RST.SubstitutionI Prd)
renameSubstitutionI (subst1, _, subst2) = do
  subst1' <- renameSubstitution subst1
  subst2' <- renameSubstitution subst2
  pure (subst1', PrdRep, subst2')



renameTermCase :: DataCodata -> CST.TermCase -> RenamerM (RST.TermCase Prd)
renameTermCase dc CST.MkTermCase { tmcase_ext, tmcase_name, tmcase_args, tmcase_term } = do
  tm' <- renameTerm PrdRep tmcase_term
  checkXtorArity tmcase_ext (tmcase_name, dc) (fst <$> tmcase_args)
  pure RST.MkTermCase { tmcase_ext = tmcase_ext
                      , tmcase_name = tmcase_name
                      , tmcase_args = second Just <$> tmcase_args
                      , tmcase_term = RST.termClosing tmcase_args tm'
                      }

termCasesToNS :: [CST.TermCase] -> DataCodata -> RenamerM NominalStructural
termCasesToNS [] _ = pure Structural
termCasesToNS ((CST.MkTermCase { tmcase_ext, tmcase_name }):_) dc = do
  (_, (ns,_)) <- lookupXtor tmcase_ext (tmcase_name, dc)
  pure ns

renameTermCaseI :: DataCodata -> CST.TermCaseI -> RenamerM (RST.TermCaseI Prd)
renameTermCaseI dc (CST.MkTermCaseI { tmcasei_ext, tmcasei_name, tmcasei_args = (bs1,(),bs2), tmcasei_term }) = do
  tm' <- renameTerm PrdRep tmcasei_term
  checkXtorArity tmcasei_ext (tmcasei_name,dc) ((fst <$> bs1) ++ [Cns] ++ (fst <$> bs2))
  pure RST.MkTermCaseI { tmcasei_ext = tmcasei_ext
                       , tmcasei_name = tmcasei_name
                       , tmcasei_args = (second Just <$> bs1, (), second Just <$> bs2)
                       -- HACK: We want to ensure that the implicit argument gets the intuitive De-Bruijn index.
                       -- termClosing doesn't support implicit arguments yet. We can emulate it for now by passing
                       -- a string that cannot be parsed as a variable (e.g. *).
                       , tmcasei_term = RST.termClosing (bs1 ++ [(Cns, MkFreeVarName "*")] ++ bs2) tm'
                       }

termCasesIToNS :: [CST.TermCaseI] -> DataCodata -> RenamerM NominalStructural
termCasesIToNS [] _ = pure Structural
termCasesIToNS ((CST.MkTermCaseI { tmcasei_ext, tmcasei_name }):_) dc = do
  (_,(ns,_)) <- lookupXtor tmcasei_ext (tmcasei_name, dc)
  pure ns

renameCommandCase :: DataCodata -> CST.CmdCase -> RenamerM RST.CmdCase
renameCommandCase dc (CST.MkCmdCase { cmdcase_ext, cmdcase_name, cmdcase_args, cmdcase_cmd}) = do
  cmd' <- renameCommand cmdcase_cmd
  checkXtorArity cmdcase_ext (cmdcase_name,dc) (fst <$> cmdcase_args)
  pure RST.MkCmdCase { cmdcase_ext = cmdcase_ext
                     , cmdcase_name = cmdcase_name
                     , cmdcase_args = second Just <$> cmdcase_args
                     , cmdcase_cmd = RST.commandClosing cmdcase_args cmd'
                     }

-- TODO: Check that all command cases use the same nominal/structural variant.
commandCasesToNS :: [CST.CmdCase] -> DataCodata -> RenamerM NominalStructural
commandCasesToNS [] _ = pure Structural
commandCasesToNS ((CST.MkCmdCase { cmdcase_ext, cmdcase_name }):_) dc = do
  (_,(ns,_)) <- lookupXtor cmdcase_ext (cmdcase_name, dc)
  pure ns

renameTerm :: PrdCnsRep pc -> CST.Term -> RenamerM (RST.Term pc)
renameTerm rep    (CST.Var loc v) =
  pure $ RST.FreeVar loc rep v
renameTerm PrdRep (CST.Xtor loc xtor subst) = do
  (_,(ns, _)) <- lookupXtor loc (xtor, Data)
  checkXtorArity loc (xtor,Data) (CST.substitutionToArity subst)
  RST.Xtor loc PrdRep ns xtor <$> renameSubstitution subst
renameTerm CnsRep (CST.Xtor loc xtor subst) = do
  (_,(ns, _)) <- lookupXtor loc (xtor, Codata)
  checkXtorArity loc (xtor,Codata) (CST.substitutionToArity subst)
  RST.Xtor loc CnsRep ns xtor <$> renameSubstitution subst
renameTerm CnsRep (CST.XMatch loc Data cases) = do
  cases' <- sequence (renameCommandCase Data <$> cases)
  ns <- commandCasesToNS cases Data
  pure $ RST.XMatch loc CnsRep ns cases'
renameTerm PrdRep (CST.XMatch loc Data _) =
  throwError (OtherError (Just loc) "Cannot lower pattern match to a producer.")
renameTerm PrdRep (CST.XMatch loc Codata cases) = do
  cases' <- sequence (renameCommandCase Codata <$> cases)
  ns <- commandCasesToNS cases Codata
  pure $ RST.XMatch loc PrdRep ns cases'
renameTerm CnsRep (CST.XMatch loc Codata _) =
  throwError (OtherError (Just loc) "Cannot lower copattern match to a consumer.")
renameTerm PrdRep (CST.MuAbs loc fv cmd) = do
  cmd' <- renameCommand cmd
  pure $ RST.MuAbs loc PrdRep (Just fv) (RST.commandClosing [(Cns,fv)] cmd')
renameTerm CnsRep (CST.MuAbs loc fv cmd) = do
  cmd' <- renameCommand cmd
  pure $ RST.MuAbs loc CnsRep (Just fv) (RST.commandClosing [(Prd,fv)] cmd')
renameTerm PrdRep (CST.Dtor loc xtor tm subst) = do
  (_,(ns, _)) <- lookupXtor loc (xtor, Codata)
  checkXtorArity loc (xtor,Codata) (CST.substitutionIToArity subst)
  tm' <- renameTerm PrdRep tm
  subst' <- renameSubstitutionI subst
  pure $ RST.Dtor loc PrdRep ns xtor tm' subst'
renameTerm CnsRep (CST.Dtor loc _xtor _tm _s)   =
  throwError (OtherError (Just loc) "Cannot lower Dtor to a consumer (TODO).")
renameTerm PrdRep (CST.Case loc tm cases)       = do
  cases' <- sequence (renameTermCase Data <$> cases)
  tm' <- renameTerm PrdRep tm
  ns <- termCasesToNS cases Data
  pure $ RST.Case loc ns tm' cases'
renameTerm CnsRep (CST.Case loc _tm _cases) =
  throwError (OtherError (Just loc) "Cannot lower Match to a consumer (TODO)")
renameTerm PrdRep (CST.Cocase loc cases) = do
  cases' <- sequence (renameTermCaseI Codata <$> cases)
  ns <- termCasesIToNS cases Codata
  pure $ RST.Cocase loc ns cases'
renameTerm CnsRep (CST.Cocase loc _cases) =
  throwError (OtherError (Just loc) "Cannot lower Comatch to a consumer (TODO)")
renameTerm PrdRep (CST.NatLit loc ns i) =
  renameNatLit loc ns i
renameTerm CnsRep (CST.NatLit loc _ns _i) =
  throwError (OtherError (Just loc) "Cannot lower NatLit to a consumer.")
renameTerm rep    (CST.TermParens _loc tm) =
  renameTerm rep tm
renameTerm rep    (CST.DtorChain pos tm dtors) =
  renameDtorChain pos tm dtors >>= renameTerm rep
renameTerm PrdRep (CST.FunApp loc fun arg) =
  renameApp loc fun arg
renameTerm CnsRep (CST.FunApp loc _fun _arg) =
  throwError (OtherError (Just loc) "Cannot lower FunApp to a consumer.")
renameTerm rep    (CST.MultiLambda loc fvs tm) =
  renameMultiLambda loc fvs tm >>= renameTerm rep
renameTerm PrdRep (CST.Lambda loc fv tm) =
  renameLambda loc fv tm
renameTerm CnsRep (CST.Lambda loc _fv _tm) =
  throwError (OtherError (Just loc) "Cannot lower Lambda to a consumer.")
renameTerm PrdRep (CST.PrimLitI64 loc i) =
  pure $ RST.PrimLitI64 loc i
renameTerm CnsRep (CST.PrimLitI64 loc _) =
  throwError (OtherError (Just loc) "Cannot lower primitive literal to a consumer.")
renameTerm PrdRep (CST.PrimLitF64 loc d) =
  pure $ RST.PrimLitF64 loc d
renameTerm CnsRep (CST.PrimLitF64 loc _) =
  throwError (OtherError (Just loc) "Cannot lower primitive literal to a consumer.")



renameDtorChain :: SourcePos -> CST.Term -> NonEmpty (XtorName, CST.SubstitutionI, SourcePos) -> RenamerM CST.Term
renameDtorChain startPos tm ((xtor, subst, endPos) :| [])   = pure $ CST.Dtor (Loc startPos endPos) xtor tm subst
renameDtorChain startPos tm ((xtor, subst, endPos) :| (x:xs)) = renameDtorChain startPos (CST.Dtor (Loc startPos endPos) xtor tm subst) (x :| xs)


-- | Lower a multi-lambda abstraction
renameMultiLambda :: Loc -> [FreeVarName] -> CST.Term -> RenamerM (CST.Term)
renameMultiLambda _ [] tm = pure tm
renameMultiLambda loc (fv:fvs) tm = CST.Lambda loc fv <$> renameMultiLambda loc fvs tm

-- | Lower a lambda abstraction.
renameLambda :: Loc -> FreeVarName -> CST.Term -> RenamerM (RST.Term Prd)
renameLambda loc var tm = do
  tm' <- renameTerm PrdRep tm
  pure $ RST.Cocase loc Nominal [ RST.MkTermCaseI loc (MkXtorName "Ap")
                                                      ([(Prd, Just var)], (), [])
                                                      (RST.termClosing [(Prd, var)] tm')
                                ]

-- | Lower a natural number literal.
renameNatLit :: Loc -> NominalStructural -> Int -> RenamerM (RST.Term Prd)
renameNatLit loc ns 0 = pure $ RST.Xtor loc PrdRep ns (MkXtorName "Z") []
renameNatLit loc ns n = do
  n' <- renameNatLit loc ns (n-1)
  pure $ RST.Xtor loc PrdRep ns (MkXtorName "S") [RST.PrdTerm n']

-- | Lower an application.
renameApp :: Loc -> CST.Term -> CST.Term -> RenamerM (RST.Term Prd)
renameApp loc fun arg = do
  fun' <- renameTerm PrdRep fun
  arg' <- renameTerm PrdRep arg
  pure $ RST.Dtor loc PrdRep Nominal (MkXtorName "Ap") fun' ([RST.PrdTerm arg'],PrdRep,[])

renameCommand :: CST.Command -> RenamerM RST.Command
renameCommand (CST.Apply loc tm1 tm2)       = RST.Apply loc <$> renameTerm PrdRep tm1 <*> renameTerm CnsRep tm2
renameCommand (CST.Print loc tm cmd)        = RST.Print loc <$> renameTerm PrdRep tm <*> renameCommand cmd
renameCommand (CST.Read loc tm)             = RST.Read loc <$> renameTerm CnsRep tm
renameCommand (CST.Jump loc fv)             = pure $ RST.Jump loc fv
renameCommand (CST.ExitSuccess loc)         = pure $ RST.ExitSuccess loc
renameCommand (CST.ExitFailure loc)         = pure $ RST.ExitFailure loc
renameCommand (CST.CommandParens _loc cmd)  = renameCommand cmd
renameCommand (CST.PrimOp loc pt op subst)  = do
  let arity = CST.substitutionToArity subst
  _ <- checkPrimOpArity loc (pt, op) arity
  RST.PrimOp loc pt op <$> renameSubstitution subst

---------------------------------------------------------------------------------
-- Check Arity of PrimOp
---------------------------------------------------------------------------------

checkPrimOpArity :: Loc -> (PrimitiveType, PrimitiveOp) -> Arity -> RenamerM ()
checkPrimOpArity loc primOp arityUsed = do
  case M.lookup primOp primOps of
    Nothing -> throwError (LowerError (Just loc) (UndefinedPrimOp primOp))
    Just aritySpecified ->
      if arityUsed /= aritySpecified then
        throwError (LowerError (Just loc) (PrimOpArityMismatch primOp aritySpecified arityUsed))
      else
        pure ()
