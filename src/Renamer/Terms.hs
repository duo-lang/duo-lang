module Renamer.Terms (renameTerm, renameCommand) where

import Control.Monad.Except (throwError)
import Data.Bifunctor ( second )
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map qualified as M
import Text.Megaparsec.Pos (SourcePos)

import Errors
import Renamer.Definition
import Renamer.SymbolTable
import Syntax.RST.Terms qualified as RST
import Syntax.CST.Terms qualified as CST
import Syntax.Common
import Utils
import Control.Monad (when)
import qualified Syntax.Common as CST
import qualified Syntax.CST.Terms as CST.Terms
import qualified Data.Text as T

---------------------------------------------------------------------------------
-- Check Arity of Xtor
---------------------------------------------------------------------------------
renameT :: PrdCns -> CST.Term -> RenamerM RST.PrdCnsTerm
renameT Prd t = RST.PrdTerm <$> renameTerm PrdRep t
renameT Cns t = RST.CnsTerm <$> renameTerm CnsRep t

-- can only be called when length ar == length tms
renameTerms :: Loc -> Arity -> [CST.Term] -> RenamerM [RST.PrdCnsTerm]
renameTerms _ [] [] = return []
renameTerms loc (a:ar) (t:tms) = do
  t' <- renameT a t
  tms' <- renameTerms loc ar tms
  return $ t' : tms'
renameTerms loc ar t = error $ "compiler bug in renameTerms, loc = " ++ show loc ++ ", ar = " ++ show ar ++ ", t = " ++ show t

---------------------------------------------------------------------------------
-- Check Arity of Xtor
---------------------------------------------------------------------------------


renameCommand :: CST.Term -> RenamerM RST.Command
renameCommand (CST.PrimCmdTerm (CST.Print loc tm cmd)) =
  RST.Print loc <$> renameTerm PrdRep tm <*> renameCommand cmd
renameCommand (CST.PrimCmdTerm (CST.Read loc tm)) =
  RST.Read loc <$> renameTerm CnsRep tm
renameCommand (CST.Var loc fv)              = pure $ RST.Jump loc fv
renameCommand (CST.PrimCmdTerm (CST.ExitSuccess loc) )  =
  pure $ RST.ExitSuccess loc
renameCommand (CST.PrimCmdTerm (CST.ExitFailure loc))
  = pure $ RST.ExitFailure loc
renameCommand (CST.TermParens _loc cmd) = renameCommand cmd
renameCommand (CST.PrimCmdTerm (CST.PrimOp loc pt op tms)) =
  do
    reqArity <- getPrimOpArity loc (pt, op)
    when (length reqArity /= length tms) $
           throwError $ LowerError (Just loc) $ PrimOpArityMismatch (pt,op) (length reqArity) (length tms)
    foo <- renameTerms loc reqArity tms
    return $ RST.PrimOp loc pt op foo
renameCommand (CST.Apply loc tm1 tm2) =
  RST.Apply loc <$> renameTerm PrdRep tm1 <*> renameTerm CnsRep tm2
renameCommand t = throwError $ LowerError (Just (CST.getLoc t)) (CmdExpected "Command expected")

getPrimOpArity :: Loc -> (PrimitiveType, PrimitiveOp) -> RenamerM Arity
getPrimOpArity loc primOp = do
  case M.lookup primOp primOps of
    Nothing -> throwError $ LowerError (Just loc) $ UndefinedPrimOp primOp
    Just aritySpecified -> return aritySpecified


-- todo : must analyze arity to cover all producer case
data TermCaseCases = AllNoStars | AllProducerStar | AllConsumerStar

analyzeTermCases :: [CST.TermCase] -> RenamerM TermCaseCases
analyzeTermCases cases | all noStar cases = return AllNoStars
analyzeTermCases cases | all oneStar cases = return AllConsumerStar
analyzeTermCases cases  = throwError $ LowerError (Just $ CST.tmcase_ext (head cases)) $ InvalidStar "Inconsistent stars"

noStar :: CST.TermCase -> Bool
noStar (CST.MkTermCase _ _ bs  _) = not (any isStar bs)

oneStar :: CST.TermCase -> Bool
oneStar (CST.MkTermCase _ _ bs  _) = length (filter isStar bs) == 1

isStar :: CST.FVOrStar -> Bool
isStar CST.FoSStar   = True
isStar _ = False



renameCommandCase :: DataCodata -> CST.TermCase -> RenamerM RST.CmdCase
renameCommandCase dc (CST.MkTermCase cmdcase_ext cmdcase_name cmdcase_args cmdcase_cmd) = do
  cmd' <- renameCommand cmdcase_cmd
  (_,XtorNameResult dc' _ ar) <- lookupXtor cmdcase_ext cmdcase_name
  when (length ar /= length cmdcase_args) $
           throwError $ LowerError (Just cmdcase_ext) $ XtorArityMismatch cmdcase_name (length ar) (length cmdcase_args)
  when (any (\x -> case x of CST.FoSStar -> True; _ -> False) cmdcase_args) $ throwError $ LowerError (Just cmdcase_ext) $ InvalidStar "Invalid star in command case"
  when (dc /= dc') $
           throwError $ OtherError (Just cmdcase_ext) "Constructor/Destructor confusion"
  let fv = (\x -> case x of CST.FoSStar -> error "compiler bug"; CST.FoSFV f -> f) <$> cmdcase_args
  let args = zip ar fv
  pure RST.MkCmdCase { cmdcase_ext = cmdcase_ext
                     , cmdcase_name = cmdcase_name
                     , cmdcase_args = second Just <$> args
                     , cmdcase_cmd = RST.commandClosing args cmd'
                     }

-- TODO: Check that all command cases use the same nominal/structural variant.
commandCasesToNS :: [CST.TermCase] -> RenamerM NominalStructural
commandCasesToNS [] = pure Structural
commandCasesToNS ((CST.MkTermCase { tmcase_ext, tmcase_name }):_) = do
  (_, XtorNameResult _ ns _) <- lookupXtor tmcase_ext tmcase_name
  pure ns

renameTermCase :: CST.TermCase -> RenamerM (RST.TermCase Prd)
renameTermCase CST.MkTermCase { tmcase_ext, tmcase_name, tmcase_args, tmcase_term } = do
  tm' <- renameTerm PrdRep tmcase_term
  (_, XtorNameResult dc _ ar) <- lookupXtor tmcase_ext tmcase_name
  when (length ar /= length tmcase_args) $
           throwError $ LowerError (Just tmcase_ext) $ XtorArityMismatch tmcase_name (length ar) (length tmcase_args)
  when (dc /= Data) $
           throwError $ OtherError (Just tmcase_ext) "Expected constructor but got destructor"
  when (any (\x -> case x of CST.FoSStar -> True; _ -> False) tmcase_args) $ throwError $ LowerError (Just tmcase_ext) $ InvalidStar "Invalid star in command case"
  let fv = (\x -> case x of CST.FoSStar -> error "compiler bug"; CST.FoSFV f -> f) <$> tmcase_args
  let args = zip ar fv
  pure RST.MkTermCase { tmcase_ext = tmcase_ext
                      , tmcase_name = tmcase_name
                      , tmcase_args = second Just <$> args
                      , tmcase_term = RST.termClosing args tm'
                      }


renameTermCaseI :: CST.TermCase -> RenamerM (RST.TermCaseI Prd)
renameTermCaseI CST.MkTermCase { tmcase_ext, tmcase_name, tmcase_args, tmcase_term } = do
  tm' <- renameTerm PrdRep tmcase_term
  (_, XtorNameResult dc _ ar) <- lookupXtor tmcase_ext tmcase_name
  when (length ar /= length tmcase_args) $
           throwError $ LowerError (Just tmcase_ext) $ XtorArityMismatch tmcase_name (length ar) (length tmcase_args)
  when (dc /= Codata) $
           throwError $ OtherError (Just tmcase_ext) "Expected Destructor but got constructor"
  (x,y) <- splitFS defaultLoc  tmcase_args -- TODO : improve Loc
  let (ar1,_:ar2) = splitAt (length x) ar
  let args1 = zip ar1 x
  let args2 = zip ar2 y
  pure RST.MkTermCaseI { tmcasei_ext = tmcase_ext
                      , tmcasei_name = tmcase_name
                      , tmcasei_args = (second Just <$> args1, (), second Just <$> args2)
                      , tmcasei_term = RST.termClosing (args1 ++ [(Cns, MkFreeVarName "*")] ++ args2) tm'
                      }

termCasesToNS :: [CST.TermCase] -> RenamerM NominalStructural
termCasesToNS [] = pure Structural
termCasesToNS ((CST.MkTermCase { tmcase_ext, tmcase_name }):_) = do
  (_, XtorNameResult _ ns _) <- lookupXtor tmcase_ext tmcase_name
  pure ns

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

isStarT :: CST.TermOrStar -> Bool
isStarT CST.ToSStar  = True
isStarT _ = False

toTm  :: CST.TermOrStar -> CST.Term
toTm (CST.ToSTerm t) = t
toTm _x = error "Compiler bug: toFV"

renameDtorChain :: SourcePos -> CST.Term -> NonEmpty (XtorName, [CST.TermOrStar], SourcePos) -> RenamerM CST.Term
renameDtorChain startPos tm ((xtor, subst, endPos) :| [])   = pure $ CST.Dtor (Loc startPos endPos) xtor tm subst
renameDtorChain startPos tm ((xtor, subst, endPos) :| (x:xs)) = renameDtorChain startPos (CST.Dtor (Loc startPos endPos) xtor tm subst) (x :| xs)

split :: Loc -> [CST.TermOrStar] -> RenamerM ([CST.Term],[CST.Term])
split loc args = do
  let numstars = length (filter isStarT args)
  when ( numstars /= 1) $ throwError (OtherError (Just loc) "Exactly one star expected" )
  let (args1,_:args2) = span (not . isStarT) args
  return (map toTm args1,map toTm args2)

splitFS :: Loc -> [CST.FVOrStar] -> RenamerM ([CST.FreeVarName],[CST.FreeVarName])
splitFS loc args = do
  let numstars = length (filter isStar args)
  when ( numstars /= 1) $ throwError (OtherError (Just loc) "Exactly one star expected" )
  let (args1,(_:args2)) = break isStar args
  return (map (\(CST.FoSFV fv) -> fv) args1,map (\(CST.FoSFV fv) -> fv) args2)


renameTerm :: PrdCnsRep pc -> CST.Term -> RenamerM (RST.Term pc)
renameTerm rep    (CST.Var loc v) =
  pure $ RST.FreeVar loc rep v
renameTerm PrdRep (CST.XtorSemi loc xtor subst Nothing) = do
  (_, XtorNameResult dc ns ar) <- lookupXtor loc xtor
  when (length ar /= length subst) $
           throwError $ LowerError (Just loc) $ XtorArityMismatch xtor (length ar) (length subst)
  when (dc /= Data) $
           throwError $ OtherError (Just loc) "The given xtor is declared as a destructor, not a constructor."
  pctms <- renameTerms loc ar subst
  return $ RST.Xtor loc PrdRep ns xtor pctms
renameTerm CnsRep (CST.XtorSemi loc xtor subst Nothing) = do
  (_, XtorNameResult dc ns ar) <- lookupXtor loc xtor
  when (length ar /= length subst) $
           throwError $ LowerError (Just loc) $ XtorArityMismatch xtor (length ar) (length subst)
  when (dc /= Codata) $
           throwError $ OtherError (Just loc) "The given xtor is declared as a constructor, not a destructor."
  pctms <- renameTerms loc ar subst
  return $ RST.Xtor loc CnsRep ns xtor pctms
renameTerm _ (CST.XtorSemi _loc _xtor _subst (Just _t)) = error "renameTerm / XTorSemi: not yet implemented"
renameTerm PrdRep (CST.XCase loc Data Nothing _) =
  throwError (OtherError (Just loc) "Cannot rename pattern match to a producer.")
renameTerm CnsRep (CST.XCase loc Codata Nothing _) =
  throwError (OtherError (Just loc) "Cannot rename copattern match to a consumer.")
renameTerm PrdRep (CST.XCase loc dc Nothing cases)  = do
  c <- analyzeTermCases cases
  case c of
    AllNoStars -> do
      cases' <- sequence (renameCommandCase dc <$> cases)
      ns <- commandCasesToNS cases
      pure $ RST.XMatch loc PrdRep ns cases'
    AllConsumerStar -> do
      cases' <- sequence (renameTermCaseI <$> cases)
      ns <- termCasesToNS cases
      pure $ RST.Cocase loc ns cases'
    AllProducerStar -> error "not yet implemented"
renameTerm CnsRep (CST.XCase loc dc Nothing cases)  = do
  c <- analyzeTermCases cases
  case c of
    AllNoStars -> do
      cases' <- sequence (renameCommandCase dc <$> cases)
      ns <- commandCasesToNS cases
      pure $ RST.XMatch loc CnsRep ns cases'
    _ -> error "not yet implemented"

renameTerm PrdRep (CST.XCase loc Data (Just t) cases)  = do
  cases' <- sequence (renameTermCase <$> cases)
  t' <- renameTerm PrdRep t
  ns <- commandCasesToNS cases
  pure $ RST.Case loc ns t' cases'
renameTerm PrdRep (CST.MuAbs loc fv cmd) = do
  cmd' <- renameCommand cmd
  pure $ RST.MuAbs loc PrdRep (Just fv) (RST.commandClosing [(Cns,fv)] cmd')
renameTerm CnsRep (CST.MuAbs loc fv cmd) = do
  cmd' <- renameCommand cmd
  pure $ RST.MuAbs loc CnsRep (Just fv) (RST.commandClosing [(Prd,fv)] cmd')

renameTerm PrdRep (CST.FunApp loc fun arg) =
  renameApp loc fun arg
renameTerm CnsRep (CST.FunApp loc _fun _arg) =
  throwError (OtherError (Just loc) "Cannot rename FunApp to a consumer.")
renameTerm rep    (CST.MultiLambda loc fvs tm) =
  renameMultiLambda loc fvs tm >>= renameTerm rep
renameTerm PrdRep (CST.Lambda loc fv tm) =
  renameLambda loc fv tm
renameTerm CnsRep (CST.Lambda loc _fv _tm) =
  throwError (OtherError (Just loc) "Cannot rename Lambda to a consumer.")
renameTerm PrdRep (CST.PrimLitI64 loc i) =
  pure $ RST.PrimLitI64 loc i
renameTerm CnsRep (CST.PrimLitI64 loc _) =
  throwError (OtherError (Just loc) "Cannot rename primitive literal to a consumer.")
renameTerm PrdRep (CST.PrimLitF64 loc d) =
  pure $ RST.PrimLitF64 loc d
renameTerm CnsRep (CST.PrimLitF64 loc _) =
  throwError (OtherError (Just loc) "Cannot rename primitive literal to a consumer.")
renameTerm PrdRep (CST.NatLit loc ns i) =
  renameNatLit loc ns i
renameTerm CnsRep (CST.NatLit loc _ns _i) =
  throwError (OtherError (Just loc) "Cannot rename NatLit to a consumer.")
renameTerm rep    (CST.TermParens _loc tm) =
  renameTerm rep tm
renameTerm PrdRep (CST.Dtor loc xtor tm subst) = do
  (_, XtorNameResult _ ns ar) <- lookupXtor loc xtor
  when (length ar /= length subst) $
           throwError $ LowerError (Just loc) $ XtorArityMismatch xtor (length ar) (length subst)
  tm' <- renameTerm PrdRep tm
  (args1,args2) <- split loc subst
  let (ar1,_:ar2) = splitAt (length args1) ar
  -- there must be exactly one star
  args1' <- renameTerms loc ar1 args1
  args2' <- renameTerms loc ar2 args2
  pure $ RST.Dtor loc PrdRep ns xtor tm' (args1',PrdRep,args2')
renameTerm CnsRep (CST.Dtor loc _xtor _tm _s)   =
  throwError (OtherError (Just loc) "Cannot rename Dtor to a consumer (TODO).")
renameTerm rep    (CST.DtorChain pos tm dtors) =
  renameDtorChain pos tm dtors >>= renameTerm rep
renameTerm _ (CST.Apply loc _ _) =  throwError (OtherError (Just loc) "Cannot rename Command to a term.")
renameTerm _ t = throwError (OtherError (Just (CST.Terms.getLoc t)) (T.pack $ "Cannot rename "++ show t ++ " to a term."))
