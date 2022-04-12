module Renamer.Terms (lowerTerm, lowerCommand) where

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
import Control.Monad (when)
import qualified Syntax.Common as CST

---------------------------------------------------------------------------------
-- Check Arity of Xtor
---------------------------------------------------------------------------------
lowerT :: PrdCns -> CST.Term -> RenamerM RST.PrdCnsTerm
lowerT Prd t = RST.PrdTerm <$> lowerTerm PrdRep t
lowerT Cns t = RST.CnsTerm <$> lowerTerm CnsRep t

-- can only be called when length ar == length tms
lowerTerms :: Loc -> Arity -> [CST.Term] -> RenamerM [RST.PrdCnsTerm]
lowerTerms _ [] [] = return []
lowerTerms loc (a:ar) (t:tms) = do
  t' <- lowerT a t
  tms' <- lowerTerms loc ar tms
  return $ t' : tms'
lowerTerms loc ar t = error $ "compiler bug in lowerTerms, loc = " ++ show loc ++ ", ar = " ++ show ar ++ ", t = " ++ show t

{-
checkXtorArity :: Loc -> (XtorName, DataCodata) -> Arity -> RenamerM ()
checkXtorArity loc (xt, dc) arityUsed = do
  (_,aritySpecified) <- lookupXtor loc (xt, dc)
  if arityUsed /= aritySpecified
    then throwError (LowerError (Just loc) (XtorArityMismatch xt aritySpecified arityUsed))
    else pure ()
-}

---------------------------------------------------------------------------------
-- Check Arity of Xtor
---------------------------------------------------------------------------------


lowerCommand :: CST.Term -> RenamerM RST.Command
lowerCommand (CST.PrimCmdTerm (CST.Print loc tm cmd)) =
  RST.Print loc <$> lowerTerm PrdRep tm <*> lowerCommand cmd
lowerCommand (CST.PrimCmdTerm (CST.Read loc tm)) =
  RST.Read loc <$> lowerTerm CnsRep tm
lowerCommand (CST.Var loc fv)              = pure $ RST.Jump loc fv
lowerCommand (CST.PrimCmdTerm (CST.ExitSuccess loc) )  =
  pure $ RST.ExitSuccess loc
lowerCommand (CST.PrimCmdTerm (CST.ExitFailure loc))
  = pure $ RST.ExitFailure loc
lowerCommand (CST.TermParens _loc cmd) = lowerCommand cmd
lowerCommand (CST.PrimCmdTerm (CST.PrimOp loc pt op tms)) =
  do
    reqArity <- getPrimOpArity loc (pt, op)
    when (length reqArity /= length tms) $
           throwError $ LowerError (Just loc) $ PrimOpArityMismatch (pt,op) (length reqArity) (length tms)
    foo <- lowerTerms loc reqArity tms
    return $ RST.PrimOp loc pt op foo
lowerCommand (CST.Apply loc tm1 tm2) =
  RST.Apply loc <$> lowerTerm PrdRep tm1 <*> lowerTerm CnsRep tm2
lowerCommand t = throwError $ LowerError (Just (CST.getLoc t)) (CmdExpected "Command expected")

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



lowerCommandCase :: DataCodata -> CST.TermCase -> RenamerM RST.CmdCase
lowerCommandCase dc (CST.MkTermCase cmdcase_ext cmdcase_name cmdcase_args cmdcase_cmd) = do
  cmd' <- lowerCommand cmdcase_cmd
  (_, ar) <- lookupXtor cmdcase_ext (cmdcase_name, dc)
  when (length ar /= length cmdcase_args) $
           throwError $ LowerError (Just cmdcase_ext) $ XtorArityMismatch cmdcase_name (length ar) (length cmdcase_args)
  when (any (\x -> case x of CST.FoSStar -> True; _ -> False) cmdcase_args) $ throwError $ LowerError (Just cmdcase_ext) $ InvalidStar "Invalid star in command case"
  let fv = (\x -> case x of CST.FoSStar -> error "compiler bug"; CST.FoSFV f -> f) <$> cmdcase_args
  let args = zip ar fv
  pure RST.MkCmdCase { cmdcase_ext = cmdcase_ext
                     , cmdcase_name = cmdcase_name
                     , cmdcase_args = second Just <$> args
                     , cmdcase_cmd = RST.commandClosing args cmd'
                     }

-- TODO: Check that all command cases use the same nominal/structural variant.
commandCasesToNS :: [CST.TermCase] -> DataCodata -> RenamerM NominalStructural
commandCasesToNS [] _ = pure Structural
commandCasesToNS ((CST.MkTermCase { tmcase_ext, tmcase_name }):_) dc =
  fst <$> lookupXtor tmcase_ext (tmcase_name, dc)

lowerTermCase :: DataCodata -> CST.TermCase -> RenamerM (RST.TermCase Prd)
lowerTermCase dc CST.MkTermCase { tmcase_ext, tmcase_name, tmcase_args, tmcase_term } = do
  tm' <- lowerTerm PrdRep tmcase_term
  (_, ar) <- lookupXtor tmcase_ext (tmcase_name, dc)
  when (length ar /= length tmcase_args) $
           throwError $ LowerError (Just tmcase_ext) $ XtorArityMismatch tmcase_name (length ar) (length tmcase_args)
  when (any (\x -> case x of CST.FoSStar -> True; _ -> False) tmcase_args) $ throwError $ LowerError (Just tmcase_ext) $ InvalidStar "Invalid star in command case"
  let fv = (\x -> case x of CST.FoSStar -> error "compiler bug"; CST.FoSFV f -> f) <$> tmcase_args
  let args = zip ar fv
  pure RST.MkTermCase { tmcase_ext = tmcase_ext
                      , tmcase_name = tmcase_name
                      , tmcase_args = second Just <$> args
                      , tmcase_term = RST.termClosing args tm'
                      }


lowerTermCaseI :: DataCodata -> CST.TermCase -> RenamerM (RST.TermCaseI Prd)
lowerTermCaseI dc CST.MkTermCase { tmcase_ext, tmcase_name, tmcase_args, tmcase_term } = do
  tm' <- lowerTerm PrdRep tmcase_term
  (_, ar) <- lookupXtor tmcase_ext (tmcase_name, dc)
  when (length ar /= length tmcase_args) $
           throwError $ LowerError (Just tmcase_ext) $ XtorArityMismatch tmcase_name (length ar) (length tmcase_args)
  (x,y) <- splitFS defaultLoc  tmcase_args -- TODO : improve Loc
  let (ar1,_:ar2) = splitAt (length x) ar
  let args1 = zip ar1 x
  let args2 = zip ar2 y
  pure RST.MkTermCaseI { tmcasei_ext = tmcase_ext
                      , tmcasei_name = tmcase_name
                      , tmcasei_args = (second Just <$> args1, (), second Just <$> args2)
                      , tmcasei_term = RST.termClosing (args1 ++ [(Cns, MkFreeVarName "*")] ++ args2) tm'
                      }

termCasesToNS :: [CST.TermCase] -> DataCodata -> RenamerM NominalStructural
termCasesToNS [] _ = pure Structural
termCasesToNS ((CST.MkTermCase { tmcase_ext, tmcase_name }):_) dc =
  fst <$> lookupXtor tmcase_ext (tmcase_name, dc)



-- | Lower a multi-lambda abstraction
lowerMultiLambda :: Loc -> [FreeVarName] -> CST.Term -> RenamerM (CST.Term)
lowerMultiLambda _ [] tm = pure tm
lowerMultiLambda loc (fv:fvs) tm = CST.Lambda loc fv <$> lowerMultiLambda loc fvs tm

-- | Lower a lambda abstraction.
lowerLambda :: Loc -> FreeVarName -> CST.Term -> RenamerM (RST.Term Prd)
lowerLambda loc var tm = do
  tm' <- lowerTerm PrdRep tm
  pure $ RST.Cocase loc Nominal [ RST.MkTermCaseI loc (MkXtorName "Ap")
                                                      ([(Prd, Just var)], (), [])
                                                      (RST.termClosing [(Prd, var)] tm')
                                ]

-- | Lower a natural number literal.
lowerNatLit :: Loc -> NominalStructural -> Int -> RenamerM (RST.Term Prd)
lowerNatLit loc ns 0 = pure $ RST.Xtor loc PrdRep ns (MkXtorName "Z") []
lowerNatLit loc ns n = do
  n' <- lowerNatLit loc ns (n-1)
  pure $ RST.Xtor loc PrdRep ns (MkXtorName "S") [RST.PrdTerm n']

-- | Lower an application.
lowerApp :: Loc -> CST.Term -> CST.Term -> RenamerM (RST.Term Prd)
lowerApp loc fun arg = do
  fun' <- lowerTerm PrdRep fun
  arg' <- lowerTerm PrdRep arg
  pure $ RST.Dtor loc PrdRep Nominal (MkXtorName "Ap") fun' ([RST.PrdTerm arg'],PrdRep,[])

isStarT :: CST.TermOrStar -> Bool
isStarT CST.ToSStar  = True
isStarT _ = False

toTm  :: CST.TermOrStar -> CST.Term
toTm (CST.ToSTerm t) = t
toTm _x = error "Compiler bug: toFV"

lowerDtorChain :: SourcePos -> CST.Term -> NonEmpty (XtorName, [CST.TermOrStar], SourcePos) -> RenamerM CST.Term
lowerDtorChain startPos tm ((xtor, subst, endPos) :| [])   = pure $ CST.Dtor (Loc startPos endPos) xtor tm subst
lowerDtorChain startPos tm ((xtor, subst, endPos) :| (x:xs)) = lowerDtorChain startPos (CST.Dtor (Loc startPos endPos) xtor tm subst) (x :| xs)

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


lowerTerm :: PrdCnsRep pc -> CST.Term -> RenamerM (RST.Term pc)
lowerTerm rep    (CST.Var loc v) =
  pure $ RST.FreeVar loc rep v

lowerTerm PrdRep (CST.XtorSemi loc xtor subst Nothing) = do
  (ns, ar) <- lookupXtor loc (xtor, Data)
  when (length ar /= length subst) $
           throwError $ LowerError (Just loc) $ XtorArityMismatch xtor (length ar) (length subst)
  pctms <- lowerTerms loc ar subst
  return $ RST.Xtor loc PrdRep ns xtor pctms
lowerTerm CnsRep (CST.XtorSemi loc xtor subst Nothing) = do
  (ns, ar) <- lookupXtor loc (xtor, Codata)
  when (length ar /= length subst) $
           throwError $ LowerError (Just loc) $ XtorArityMismatch xtor (length ar) (length subst)
  pctms <- lowerTerms loc ar subst
  return $ RST.Xtor loc CnsRep ns xtor pctms
lowerTerm _ (CST.XtorSemi _loc _xtor _subst (Just _t)) = error "lowerTerm / XTorSemi: not yet implemented"
lowerTerm PrdRep (CST.XCase loc Data Nothing _) =
  throwError (OtherError (Just loc) "Cannot lower pattern match to a producer.")
lowerTerm CnsRep (CST.XCase loc Codata Nothing _) =
  throwError (OtherError (Just loc) "Cannot lower copattern match to a consumer.")
lowerTerm PrdRep (CST.XCase loc dc Nothing cases)  = do
  c <- analyzeTermCases cases
  case c of
    AllNoStars -> do
      cases' <- sequence (lowerCommandCase dc <$> cases)
      ns <- commandCasesToNS cases dc
      pure $ RST.XMatch loc PrdRep ns cases'
    AllConsumerStar -> do
      cases' <- sequence (lowerTermCaseI Codata <$> cases)
      ns <- termCasesToNS cases Codata
      pure $ RST.Cocase loc ns cases'
    _ -> error "not yet implemented"
lowerTerm CnsRep (CST.XCase loc dc Nothing cases)  = do
  c <- analyzeTermCases cases
  case c of
    AllNoStars -> do
      cases' <- sequence (lowerCommandCase dc <$> cases)
      ns <- commandCasesToNS cases dc
      pure $ RST.XMatch loc CnsRep ns cases'
    _ -> error "not yet implemented"

lowerTerm PrdRep (CST.XCase loc Data (Just t) cases)  = do
  cases' <- sequence (lowerTermCase Data <$> cases)
  t' <- lowerTerm PrdRep t
  ns <- commandCasesToNS cases Data
  pure $ RST.Case loc ns t' cases'
lowerTerm PrdRep (CST.MuAbs loc fv cmd) = do
  cmd' <- lowerCommand cmd
  pure $ RST.MuAbs loc PrdRep (Just fv) (RST.commandClosing [(Cns,fv)] cmd')
lowerTerm CnsRep (CST.MuAbs loc fv cmd) = do
  cmd' <- lowerCommand cmd
  pure $ RST.MuAbs loc CnsRep (Just fv) (RST.commandClosing [(Prd,fv)] cmd')

lowerTerm PrdRep (CST.FunApp loc fun arg) =
  lowerApp loc fun arg
lowerTerm CnsRep (CST.FunApp loc _fun _arg) =
  throwError (OtherError (Just loc) "Cannot lower FunApp to a consumer.")
lowerTerm rep    (CST.MultiLambda loc fvs tm) =
  lowerMultiLambda loc fvs tm >>= lowerTerm rep
lowerTerm PrdRep (CST.Lambda loc fv tm) =
  lowerLambda loc fv tm
lowerTerm CnsRep (CST.Lambda loc _fv _tm) =
  throwError (OtherError (Just loc) "Cannot lower Lambda to a consumer.")
lowerTerm PrdRep (CST.PrimLitI64 loc i) =
  pure $ RST.PrimLitI64 loc i
lowerTerm CnsRep (CST.PrimLitI64 loc _) =
  throwError (OtherError (Just loc) "Cannot lower primitive literal to a consumer.")
lowerTerm PrdRep (CST.PrimLitF64 loc d) =
  pure $ RST.PrimLitF64 loc d
lowerTerm CnsRep (CST.PrimLitF64 loc _) =
  throwError (OtherError (Just loc) "Cannot lower primitive literal to a consumer.")
lowerTerm PrdRep (CST.NatLit loc ns i) =
  lowerNatLit loc ns i
lowerTerm CnsRep (CST.NatLit loc _ns _i) =
  throwError (OtherError (Just loc) "Cannot lower NatLit to a consumer.")
lowerTerm rep    (CST.TermParens _loc tm) =
  lowerTerm rep tm
lowerTerm PrdRep (CST.Dtor loc xtor tm subst) = do
  (ns, ar) <- lookupXtor loc (xtor, Codata)
  when (length ar /= length subst) $
           throwError $ LowerError (Just loc) $ XtorArityMismatch xtor (length ar) (length subst)
  tm' <- lowerTerm PrdRep tm
  (args1,args2) <- split loc subst
  let (ar1,_:ar2) = splitAt (length args1) ar
  -- there must be exactly one star
  args1' <- lowerTerms loc ar1 args1
  args2' <- lowerTerms loc ar2 args2
  pure $ RST.Dtor loc PrdRep ns xtor tm' (args1',PrdRep,args2')
lowerTerm CnsRep (CST.Dtor loc _xtor _tm _s)   =
  throwError (OtherError (Just loc) "Cannot lower Dtor to a consumer (TODO).")
lowerTerm rep    (CST.DtorChain pos tm dtors) =
  lowerDtorChain pos tm dtors >>= lowerTerm rep
lowerTerm rep t = error $ "lowerTerm not yet implemented for " ++ show t ++ " in rep: " ++ show rep
