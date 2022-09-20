module Translate.EmbedRST
  ( reparseTerm
  , reparsePCTerm
  , reparseCommand
  , reparseDecl
  , reparseModule
  , reparseSubst
  , reparseSubstI
  , reparseCmdCase
  , reparseTermCase
  , reparseTermCaseI
  , reparseInstanceCase
  -- Types
  , EmbedRST(..)
  ) where


import Control.Monad.State
import Data.Bifunctor
import Data.Text qualified as T
import Data.Maybe (fromJust)

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
    ( BinOp(InterOp, CustomOp, UnionOp),
      FreeVarName(MkFreeVarName),
      MethodName(unMethodName),
      RecTVar(MkRecTVar),
      RnTypeName(MkRnTypeName, rnTnName),
      SkolemTVar(MkSkolemTVar),
      PrimName(..),
      printName,
      readName,
      exitSuccessName,
      exitFailureName,
      i64AddName,
      i64SubName,
      i64MulName,
      i64DivName,
      i64ModName,
      f64AddName,
      f64SubName,
      f64MulName,
      f64DivName,
      charPrependName,
      stringAppendName,
      TyOpName(MkTyOpName),
      TypeName(MkTypeName),
      XtorName(MkXtorName) )

---------------------------------------------------------------------------------
-- These functions  translate a locally nameless term into a named representation.
--
-- Use only for prettyprinting! These functions only "undo" the steps in the parser
-- and do not fulfil any semantic properties w.r.t shadowing etc.!
---------------------------------------------------------------------------------

freeVarNamesToXtorArgs :: [(PrdCns, Maybe FreeVarName)] -> RST.Substitution
freeVarNamesToXtorArgs bs = f <$> bs
  where
    f (Prd, Nothing) = error "Create Names first!"
    f (Prd, Just fv) = RST.PrdTerm $ RST.FreeVar defaultLoc PrdRep fv
    f (Cns, Nothing) = error "Create Names first!"
    f (Cns, Just fv) = RST.CnsTerm $ RST.FreeVar defaultLoc CnsRep fv

openTermCase :: RST.TermCase pc -> RST.TermCase pc
openTermCase RST.MkTermCase { tmcase_loc, tmcase_pat = RST.XtorPat loc xt args , tmcase_term } =
    RST.MkTermCase { tmcase_loc = tmcase_loc
                   , tmcase_pat = RST.XtorPat loc xt args
                   , tmcase_term = RST.termOpening (freeVarNamesToXtorArgs args) (openTermComplete tmcase_term)
                   }

openTermCaseI :: RST.TermCaseI pc -> RST.TermCaseI pc
openTermCaseI RST.MkTermCaseI { tmcasei_loc, tmcasei_pat = RST.XtorPatI loc xt (as1, (), as2), tmcasei_term } =
  RST.MkTermCaseI { tmcasei_loc = tmcasei_loc
                  , tmcasei_pat = RST.XtorPatI loc xt (as1, (), as2)
                  , tmcasei_term = RST.termOpening (freeVarNamesToXtorArgs (as1 ++ [(Cns, Nothing)] ++ as2)) (openTermComplete tmcasei_term)
                  }

openCmdCase :: RST.CmdCase -> RST.CmdCase
openCmdCase RST.MkCmdCase { cmdcase_loc, cmdcase_pat = RST.XtorPat loc xt args, cmdcase_cmd } =
  RST.MkCmdCase { cmdcase_loc = cmdcase_loc
                , cmdcase_pat = RST.XtorPat loc xt args
                , cmdcase_cmd = RST.commandOpening (freeVarNamesToXtorArgs args) (openCommandComplete cmdcase_cmd)
                }

openInstanceCase :: RST.InstanceCase -> RST.InstanceCase
openInstanceCase RST.MkInstanceCase { instancecase_loc, instancecase_pat = pat@(RST.XtorPat _loc _xt args), instancecase_cmd } =
  RST.MkInstanceCase { instancecase_loc = instancecase_loc
                     , instancecase_pat = pat
                     , instancecase_cmd = RST.commandOpening (freeVarNamesToXtorArgs args) (openCommandComplete instancecase_cmd)
                     }

openPCTermComplete :: RST.PrdCnsTerm -> RST.PrdCnsTerm
openPCTermComplete (RST.PrdTerm tm) = RST.PrdTerm $ openTermComplete tm
openPCTermComplete (RST.CnsTerm tm) = RST.CnsTerm $ openTermComplete tm

openTermComplete :: RST.Term pc -> RST.Term pc
-- Core constructs
openTermComplete (RST.BoundVar loc pc idx) =
  RST.BoundVar loc pc idx
openTermComplete (RST.FreeVar loc pc v) =
  RST.FreeVar loc pc v
openTermComplete (RST.Xtor loc pc ns xt args) =
  RST.Xtor loc pc ns xt (openPCTermComplete <$> args)
openTermComplete (RST.XCase loc pc ns cases) =
  RST.XCase loc pc ns (openCmdCase <$> cases)
openTermComplete (RST.MuAbs loc PrdRep (Just fv) cmd) =
  RST.MuAbs loc PrdRep (Just fv) (RST.commandOpening [RST.CnsTerm (RST.FreeVar defaultLoc CnsRep fv)] (openCommandComplete cmd))
openTermComplete (RST.MuAbs loc CnsRep (Just fv) cmd) =
  RST.MuAbs loc CnsRep (Just fv) (RST.commandOpening [RST.PrdTerm (RST.FreeVar defaultLoc PrdRep fv)] (openCommandComplete cmd))
openTermComplete (RST.MuAbs _ _ Nothing _) =
  error "Create names first!"
-- Syntactic sugar
openTermComplete (RST.Semi loc rep ns xt (args1, pcrep, args2) t) =
  RST.Semi loc rep ns xt (openPCTermComplete <$> args1, pcrep, openPCTermComplete <$> args2) (openTermComplete t)
openTermComplete (RST.Dtor loc rep ns xt t (args1,pcrep,args2)) =
  RST.Dtor loc rep ns xt (openTermComplete t) (openPCTermComplete <$> args1,pcrep, openPCTermComplete <$> args2)
openTermComplete (RST.CaseOf loc rep ns t cases) =
  RST.CaseOf loc rep ns (openTermComplete t) (openTermCase <$> cases)
openTermComplete (RST.CocaseOf loc rep ns t cases) =
  RST.CocaseOf loc rep ns (openTermComplete t) (openTermCase <$> cases)
openTermComplete (RST.CaseI loc rep ns cases) =
  RST.CaseI loc rep ns (openTermCaseI <$> cases)
openTermComplete (RST.CocaseI loc rep ns cocases) =
  RST.CocaseI loc rep ns (openTermCaseI <$> cocases)
openTermComplete (RST.Lambda loc pc fv tm) =
  let
    tm' = openTermComplete tm
    tm'' = case pc of PrdRep -> RST.termOpening [RST.PrdTerm (RST.FreeVar defaultLoc PrdRep fv)] tm'
                      CnsRep -> RST.termOpening [RST.CnsTerm (RST.FreeVar defaultLoc CnsRep fv)] tm'

  in
  RST.Lambda loc pc fv tm''
-- Primitive constructs
openTermComplete (RST.PrimLitI64 loc i) =
  RST.PrimLitI64 loc i
openTermComplete (RST.PrimLitF64 loc d) =
  RST.PrimLitF64 loc d
openTermComplete (RST.PrimLitChar loc d) =
  RST.PrimLitChar loc d
openTermComplete (RST.PrimLitString loc d) =
  RST.PrimLitString loc d

openCommandComplete :: RST.Command -> RST.Command
openCommandComplete (RST.Apply loc t1 t2) =
  RST.Apply loc (openTermComplete t1) (openTermComplete t2)
openCommandComplete (RST.Print loc t cmd) =
  RST.Print loc (openTermComplete t) (openCommandComplete cmd)
openCommandComplete (RST.Read loc cns) =
  RST.Read loc (openTermComplete cns)
openCommandComplete (RST.Jump loc fv) =
  RST.Jump loc fv
openCommandComplete (RST.Method loc mn cn subst) =
  RST.Method loc mn cn (openPCTermComplete <$> subst)
openCommandComplete (RST.ExitSuccess loc) =
  RST.ExitSuccess loc
openCommandComplete (RST.ExitFailure loc) =
  RST.ExitFailure loc
openCommandComplete (RST.PrimOp loc op subst) =
  RST.PrimOp loc op (openPCTermComplete <$> subst)
openCommandComplete (RST.CaseOfCmd loc ns tm cases) =
  RST.CaseOfCmd loc ns (openTermComplete tm) (openCmdCase <$> cases)
openCommandComplete (RST.CocaseOfCmd loc ns tm cases) =
  RST.CocaseOfCmd loc ns (openTermComplete tm) (openCmdCase <$> cases)
openCommandComplete (RST.CaseOfI loc rep ns tm cases) =
  RST.CaseOfI loc rep ns (openTermComplete tm) (openTermCaseI <$> cases)
openCommandComplete (RST.CocaseOfI loc rep ns tm cases) =
  RST.CocaseOfI loc rep ns (openTermComplete tm) (openTermCaseI <$> cases)

---------------------------------------------------------------------------------
-- CreateNames Monad
---------------------------------------------------------------------------------

type CreateNameM a = State ([FreeVarName],[FreeVarName]) a

names :: ([FreeVarName], [FreeVarName])
names =  ((\y -> MkFreeVarName ("x" <> T.pack (show y))) <$> [(1 :: Int)..]
         ,(\y -> MkFreeVarName ("k" <> T.pack (show y))) <$> [(1 :: Int)..])

fresh :: PrdCns -> CreateNameM (Maybe FreeVarName)
fresh Prd = do
  var <- gets (head . fst)
  modify (first tail)
  pure (Just var)
fresh Cns = do
  var  <- gets (head . snd)
  modify (second tail)
  pure (Just var)

class CreateNames a where
  createNames :: a -> CreateNameM a

instance CreateNames RST.PrdCnsTerm where
  createNames :: RST.PrdCnsTerm -> CreateNameM RST.PrdCnsTerm
  createNames (RST.PrdTerm tm) = RST.PrdTerm <$> createNames tm
  createNames (RST.CnsTerm tm) = RST.CnsTerm <$> createNames tm

instance CreateNames RST.Substitution where
  createNames :: RST.Substitution  -> CreateNameM RST.Substitution
  createNames = mapM createNames

instance CreateNames (RST.Term pc) where
  createNames :: RST.Term pc -> CreateNameM (RST.Term pc)
  -- Core constructs
  createNames (RST.BoundVar loc pc idx) =
    pure $ RST.BoundVar loc pc idx
  createNames (RST.FreeVar loc pc nm) =
    pure $ RST.FreeVar loc pc nm
  createNames (RST.Xtor loc pc ns xt subst) = do
    subst' <- createNames subst
    pure $ RST.Xtor loc pc ns xt subst'
  createNames (RST.XCase loc pc ns cases) = do
    cases' <- mapM createNames cases
    pure $ RST.XCase loc pc ns cases'
  createNames (RST.MuAbs loc pc _ cmd) = do
    cmd' <- createNames cmd
    var <- fresh (case pc of PrdRep -> Cns; CnsRep -> Prd)
    pure $ RST.MuAbs loc pc var cmd'
  -- Syntactic sugar
  createNames (RST.Semi loc pc ns xt (subst1,pcrep,subst2) e) = do
    e' <- createNames e
    subst1' <- createNames subst1
    subst2' <- createNames subst2
    pure $ RST.Semi loc pc ns xt (subst1', pcrep, subst2') e'
  createNames (RST.Dtor loc pc ns xt e (subst1,pcrep,subst2)) = do
    e' <- createNames e
    subst1' <- createNames subst1
    subst2' <- createNames subst2
    pure $ RST.Dtor loc pc ns xt e' (subst1',pcrep,subst2')
  createNames (RST.CaseOf loc rep ns e cases) = do
    e' <- createNames e
    cases' <- sequence (createNames <$> cases)
    pure $ RST.CaseOf loc rep ns e' cases'
  createNames (RST.CocaseOf loc rep ns e cases) = do
    e' <- createNames e
    cases' <- sequence (createNames <$> cases)
    pure $ RST.CocaseOf loc rep ns e' cases'
  createNames (RST.CaseI loc rep ns cases) = do
    cases' <- sequence (createNames <$> cases)
    pure $ RST.CaseI loc rep ns cases'
  createNames (RST.CocaseI loc rep ns cases) = do
    cases' <- sequence (createNames <$> cases)
    pure $ RST.CocaseI loc rep ns cases'
  createNames (RST.Lambda loc rep fvs tm) = do
    tm' <- createNames tm
    pure $ RST.Lambda loc rep fvs tm'
  -- Primitive constructs
  createNames (RST.PrimLitI64 loc i) =
    pure (RST.PrimLitI64 loc i)
  createNames (RST.PrimLitF64 loc d) =
    pure (RST.PrimLitF64 loc d)
  createNames (RST.PrimLitChar loc d) =
    pure (RST.PrimLitChar loc d)
  createNames (RST.PrimLitString loc d) =
    pure (RST.PrimLitString loc d)

instance CreateNames RST.Command where
  createNames :: RST.Command -> CreateNameM RST.Command
  createNames (RST.ExitSuccess loc) =
    pure $ RST.ExitSuccess loc
  createNames (RST.ExitFailure loc) =
    pure $ RST.ExitFailure loc
  createNames (RST.Jump loc fv) =
    pure $ RST.Jump loc fv
  createNames (RST.Method loc mn cn subst) = do
    subst' <- sequence $ createNames <$> subst
    pure $ RST.Method loc mn cn subst'
  createNames (RST.Apply loc prd cns) = do
    prd' <- createNames prd
    cns' <- createNames cns
    pure $ RST.Apply loc prd' cns'
  createNames (RST.Print loc prd cmd) = do
    prd' <- createNames prd
    cmd' <- createNames cmd
    pure $ RST.Print loc prd' cmd'
  createNames (RST.Read loc cns) = do
    cns' <- createNames cns
    pure $ RST.Read loc cns'
  createNames (RST.PrimOp loc op subst) = do
    subst' <- sequence $ createNames <$> subst
    pure $ RST.PrimOp loc op subst'
  createNames (RST.CaseOfCmd loc ns tm cases) = do
    tm' <- createNames tm
    cases' <- sequence $ createNames <$> cases
    pure $ RST.CaseOfCmd loc ns tm' cases'
  createNames (RST.CocaseOfCmd loc ns tm cases) = do
    tm' <- createNames tm
    cases' <- sequence $ createNames <$> cases
    pure $ RST.CocaseOfCmd loc ns tm' cases'
  createNames (RST.CaseOfI loc rep ns tm cases) = do
    tm' <- createNames tm
    cases' <- sequence $ createNames <$> cases
    pure $ RST.CaseOfI loc rep ns tm' cases'
  createNames (RST.CocaseOfI loc rep ns tm cases) = do
    tm' <- createNames tm
    cases' <- sequence $ createNames <$> cases
    pure $ RST.CocaseOfI loc rep ns tm' cases'

instance CreateNames RST.Pattern where
  createNames :: RST.Pattern -> CreateNameM RST.Pattern
  createNames (RST.XtorPat loc xt args) = do
    args' <- sequence $ (\(pc,_) -> fresh pc >>= \v -> return (pc,v)) <$> args
    pure $ RST.XtorPat loc xt args'

instance CreateNames RST.PatternI where
  createNames :: RST.PatternI -> CreateNameM RST.PatternI
  createNames (RST.XtorPatI loc xt (as1, (), as2)) = do
    let f (pc,_) = fresh pc >>= \v -> return (pc,v)
    as1' <- sequence $ f <$> as1
    as2' <- sequence $ f <$> as2
    pure $ RST.XtorPatI loc xt (as1', (), as2')

instance CreateNames RST.CmdCase where
  createNames :: RST.CmdCase -> CreateNameM RST.CmdCase
  createNames RST.MkCmdCase { cmdcase_loc, cmdcase_pat, cmdcase_cmd } = do
    pat' <- createNames cmdcase_pat
    cmd' <- createNames cmdcase_cmd
    pure $ RST.MkCmdCase cmdcase_loc pat' cmd'

instance CreateNames (RST.TermCase pc) where
  createNames :: RST.TermCase pc -> CreateNameM (RST.TermCase pc)
  createNames RST.MkTermCase { tmcase_loc, tmcase_pat, tmcase_term } = do
    term <- createNames tmcase_term
    pat <- createNames tmcase_pat
    pure $ RST.MkTermCase tmcase_loc pat term

instance CreateNames (RST.TermCaseI pc) where
  createNames :: RST.TermCaseI pc -> CreateNameM (RST.TermCaseI pc)
  createNames RST.MkTermCaseI { tmcasei_loc, tmcasei_pat, tmcasei_term } = do
    term <- createNames tmcasei_term
    pat <- createNames tmcasei_pat
    pure $ RST.MkTermCaseI tmcasei_loc pat term

instance CreateNames RST.InstanceCase where
  createNames :: RST.InstanceCase -> CreateNameM RST.InstanceCase
  createNames RST.MkInstanceCase { instancecase_loc, instancecase_pat, instancecase_cmd } = do
    pat' <- createNames instancecase_pat
    cmd' <- createNames instancecase_cmd
    pure $ RST.MkInstanceCase instancecase_loc pat' cmd'

---------------------------------------------------------------------------------
-- CreateNames Monad
---------------------------------------------------------------------------------

isNumSTermRST :: RST.Term pc -> Maybe Int
isNumSTermRST (RST.Xtor _ PrdRep CST.Nominal (MkXtorName "Z") []) = Just 0
isNumSTermRST (RST.Xtor _ PrdRep CST.Nominal (MkXtorName "S") [RST.PrdTerm n]) = case isNumSTermRST n of
  Nothing -> Nothing
  Just n -> Just (n + 1)
isNumSTermRST _ = Nothing

---------------------------------------------------------------------------------
-- A typeclass for embedding RST.X into CST.X
---------------------------------------------------------------------------------

class EmbedRST a b | a -> b where
  embedRST :: a -> b

---------------------------------------------------------------------------------
-- EmbedTST implementation for terms
---------------------------------------------------------------------------------

instance EmbedRST (RST.Term pc) CST.Term where
  embedRST :: RST.Term pc -> CST.Term
  embedRST (isNumSTermRST -> Just i) =
    CST.NatLit defaultLoc CST.Nominal i
  -- Core constructs
  embedRST RST.BoundVar{} =
    error "Should have been removed by opening"
  embedRST (RST.FreeVar loc _ fv) =
    CST.Var loc fv
  embedRST (RST.Xtor loc _ _ xt subst) =
    CST.Xtor loc xt (CST.ToSTerm <$> embedRST subst)
  embedRST (RST.XCase loc PrdRep _ cases) =
    CST.Cocase loc (embedRST <$> cases)
  embedRST (RST.XCase loc CnsRep _ cases) =
    CST.Case loc (embedRST <$> cases)
  embedRST (RST.MuAbs loc _ fv cmd) =
    CST.MuAbs loc (fromJust fv) (embedRST cmd)
  -- Syntactic sugar
  embedRST (RST.Semi loc _ _ (MkXtorName "CoAp")  ([RST.CnsTerm t],CnsRep,[]) tm) =
    CST.FunApp loc (embedRST tm) (embedRST t)
  embedRST (RST.Semi _loc _ _ (MkXtorName "CoAp")  other _tm) =
    error $ "embed: " ++ show  other
  embedRST (RST.Semi loc _ _ xt substi tm) =
    CST.Semi loc xt (embedRST substi) (embedRST tm)
  embedRST (RST.Dtor loc _ _ (MkXtorName "Ap") tm ([RST.PrdTerm t],PrdRep,[])) =
    CST.FunApp loc (embedRST tm) (embedRST t)
  embedRST (RST.Dtor loc _ _ xt tm substi) =
    CST.Dtor loc xt (embedRST tm) (embedRST substi)
  embedRST (RST.CaseOf loc _ _ tm cases) =
    CST.CaseOf loc (embedRST tm) (embedRST <$> cases)
  embedRST (RST.CocaseOf loc _ _ tm cases) =
    CST.CocaseOf loc (embedRST tm) (embedRST <$> cases)
  embedRST (RST.CaseI loc _ _ cases) =
    CST.Case loc (embedRST <$> cases)
  embedRST (RST.CocaseI loc _ _ cases) =
    CST.Cocase loc (embedRST <$> cases)
  embedRST (RST.Lambda loc PrdRep fvs tm) =
    CST.Lambda loc fvs (embedRST tm)
  embedRST (RST.Lambda loc CnsRep fvs tm) =
    CST.CoLambda loc fvs (embedRST tm)
  embedRST (RST.PrimLitI64 loc i) =
    CST.PrimLitI64 loc i
  embedRST (RST.PrimLitF64 loc d) =
    CST.PrimLitF64 loc d
  embedRST (RST.PrimLitChar loc d) =
    CST.PrimLitChar loc d
  embedRST (RST.PrimLitString loc d) =
    CST.PrimLitString loc d


instance EmbedRST RST.PrdCnsTerm CST.Term where
  embedRST :: RST.PrdCnsTerm -> CST.Term
  embedRST (RST.PrdTerm tm) = embedRST tm
  embedRST (RST.CnsTerm tm) = embedRST tm

instance EmbedRST RST.Substitution [CST.Term] where
  embedRST :: RST.Substitution -> [CST.Term]
  embedRST = fmap embedRST

instance EmbedRST (RST.SubstitutionI pc) [CST.TermOrStar] where
  embedRST :: RST.SubstitutionI pc -> [CST.TermOrStar]
  embedRST (subst1,PrdRep,subst2) = (CST.ToSTerm <$> embedRST subst1) ++ [CST.ToSStar] ++ (CST.ToSTerm <$> embedRST subst2)
  embedRST (subst1,CnsRep,subst2) = (CST.ToSTerm <$> embedRST subst1) ++ [CST.ToSStar] ++ (CST.ToSTerm <$> embedRST subst2)

instance EmbedRST RST.Command CST.Term where
  embedRST :: RST.Command -> CST.Term
  embedRST (RST.Apply loc prd cns) =
    CST.Apply loc (embedRST prd) (embedRST cns)
  embedRST (RST.Print loc tm cmd) =
    CST.PrimTerm loc printName [embedRST tm, embedRST cmd]
  embedRST (RST.Read loc cns) =
    CST.PrimTerm loc readName [embedRST cns]
  embedRST (RST.Jump loc fv) =
    CST.Var loc fv
  embedRST (RST.Method loc mn _cn subst) =
    CST.Xtor loc (MkXtorName $ unMethodName mn) (CST.ToSTerm <$> embedRST subst)
  embedRST (RST.ExitSuccess loc) =
    CST.PrimTerm loc exitSuccessName []
  embedRST (RST.ExitFailure loc) =
    CST.PrimTerm loc exitFailureName []
  embedRST (RST.PrimOp loc op subst) =
    CST.PrimTerm loc (embedRST op) (embedRST subst)
  embedRST (RST.CaseOfCmd loc _ns tm cases) =
    CST.CaseOf loc (embedRST tm) (embedRST <$> cases)
  embedRST (RST.CocaseOfCmd loc _ns tm cases) =
    CST.CocaseOf loc (embedRST tm) (embedRST <$> cases)
  embedRST (RST.CaseOfI loc _rep _ns tm cases) =
    CST.CaseOf loc (embedRST tm) (embedRST <$> cases)
  embedRST (RST.CocaseOfI loc _rep _ns tm cases) =
    CST.CocaseOf loc (embedRST tm) (embedRST <$> cases)

instance EmbedRST RST.PrimitiveOp PrimName where
  embedRST :: RST.PrimitiveOp -> PrimName
  embedRST RST.I64Add = i64AddName
  embedRST RST.I64Sub = i64SubName
  embedRST RST.I64Mul = i64MulName
  embedRST RST.I64Div = i64DivName
  embedRST RST.I64Mod = i64ModName
  embedRST RST.F64Add = f64AddName
  embedRST RST.F64Sub = f64SubName
  embedRST RST.F64Mul = f64MulName
  embedRST RST.F64Div = f64DivName
  embedRST RST.CharPrepend = charPrependName
  embedRST RST.StringAppend = stringAppendName

instance EmbedRST RST.Pattern CST.Pattern where
  embedRST :: RST.Pattern -> CST.Pattern
  embedRST (RST.XtorPat loc xt args) =
    CST.PatXtor loc xt (CST.PatVar loc . fromJust . snd <$> args)

instance EmbedRST RST.PatternI CST.Pattern where
  embedRST :: RST.PatternI -> CST.Pattern
  embedRST (RST.XtorPatI loc xt (as1,_,as2)) =
    CST.PatXtor loc xt ((CST.PatVar loc . fromJust . snd <$> as1) ++ [CST.PatStar loc] ++ (CST.PatVar loc . fromJust . snd  <$> as2))

instance EmbedRST RST.CmdCase CST.TermCase where
  embedRST :: RST.CmdCase -> CST.TermCase
  embedRST RST.MkCmdCase { cmdcase_loc, cmdcase_pat, cmdcase_cmd } =
    CST.MkTermCase { tmcase_loc = cmdcase_loc
                  , tmcase_pat = embedRST cmdcase_pat
                  , tmcase_term = embedRST cmdcase_cmd
                  }

instance EmbedRST (RST.TermCase pc) CST.TermCase where
  embedRST :: RST.TermCase pc -> CST.TermCase
  embedRST RST.MkTermCase { tmcase_loc, tmcase_pat, tmcase_term } =
    CST.MkTermCase { tmcase_loc = tmcase_loc
                  , tmcase_pat = embedRST tmcase_pat
                  , tmcase_term = embedRST tmcase_term}

instance EmbedRST (RST.TermCaseI pc) CST.TermCase where
  embedRST :: RST.TermCaseI pc -> CST.TermCase
  embedRST RST.MkTermCaseI { tmcasei_loc, tmcasei_pat, tmcasei_term } =
    CST.MkTermCase { tmcase_loc = tmcasei_loc
                  , tmcase_pat = embedRST tmcasei_pat
                  , tmcase_term = embedRST tmcasei_term
                  }

instance EmbedRST RST.InstanceCase CST.TermCase where
  embedRST :: RST.InstanceCase -> CST.TermCase
  embedRST RST.MkInstanceCase { instancecase_loc, instancecase_pat, instancecase_cmd } =
    CST.MkTermCase { tmcase_loc = instancecase_loc
                  , tmcase_pat = embedRST instancecase_pat
                  , tmcase_term = embedRST instancecase_cmd
                  }

---------------------------------------------------------------------------------
-- EmbedTST implementation for types
---------------------------------------------------------------------------------

instance EmbedRST (RST.PrdCnsType pol) CST.PrdCnsTyp where
  embedRST :: RST.PrdCnsType pol -> CST.PrdCnsTyp
  embedRST (RST.PrdCnsType PrdRep ty) = CST.PrdType (embedRST ty)
  embedRST (RST.PrdCnsType CnsRep ty) = CST.CnsType (embedRST ty)

instance EmbedRST (RST.LinearContext pol) CST.LinearContext where
  embedRST :: RST.LinearContext pol -> CST.LinearContext
  embedRST = fmap embedRST

instance EmbedRST (RST.XtorSig pol) CST.XtorSig where
  embedRST :: RST.XtorSig pol -> CST.XtorSig
  embedRST RST.MkXtorSig { sig_name, sig_args } =
    CST.MkXtorSig { sig_name = sig_name
                  , sig_args = embedRST sig_args
                  }

instance EmbedRST (RST.MethodSig pol) CST.XtorSig where
  embedRST :: RST.MethodSig pol -> CST.XtorSig
  embedRST RST.MkMethodSig { msig_name, msig_args } =
    CST.MkXtorSig { sig_name = MkXtorName $ unMethodName msig_name
                  , sig_args = embedRST msig_args
                  }

instance EmbedRST [RST.VariantType pol] [CST.Typ] where
  embedRST :: [RST.VariantType pol] -> [CST.Typ]
  embedRST = fmap embedRST

instance EmbedRST (RST.VariantType pol) CST.Typ where
  embedRST :: RST.VariantType pol -> CST.Typ
  embedRST (RST.CovariantType ty) = embedRST ty
  embedRST (RST.ContravariantType ty) = embedRST ty

resugarType :: RST.Typ pol -> Maybe CST.Typ
resugarType (RST.TyNominal loc _ MkRnTypeName { rnTnName = MkTypeName "Fun" } [RST.ContravariantType tl, RST.CovariantType tr]) =
  Just (CST.TyBinOp loc (embedRST tl) (CustomOp (MkTyOpName "->")) (embedRST tr))
resugarType (RST.TyNominal loc _ MkRnTypeName { rnTnName = MkTypeName "CoFun" } [RST.CovariantType tl, RST.ContravariantType tr]) =
  Just (CST.TyBinOp loc (embedRST tl) (CustomOp (MkTyOpName "-<")) (embedRST tr))
resugarType (RST.TyNominal loc _ MkRnTypeName { rnTnName = MkTypeName "Par" } [RST.CovariantType t1, RST.CovariantType t2]) =
  Just (CST.TyBinOp loc (embedRST t1) (CustomOp (MkTyOpName "⅋")) (embedRST t2))
resugarType _ = Nothing

embedRecTVar :: RecTVar -> SkolemTVar
embedRecTVar (MkRecTVar n) = MkSkolemTVar n

instance EmbedRST (RST.Typ pol) CST.Typ where
  embedRST :: RST.Typ pol -> CST.Typ
  embedRST (resugarType -> Just ty) = ty
  embedRST (RST.TyUniVar loc _ tv) =
    CST.TyUniVar loc tv
  embedRST (RST.TySkolemVar loc _ tv) = 
    CST.TySkolemVar loc tv
  embedRST (RST.TyRecVar loc _ tv) = 
    CST.TySkolemVar loc $ embedRecTVar tv
  embedRST (RST.TyData loc _ xtors) =
    CST.TyXData loc CST.Data (embedRST <$> xtors)
  embedRST (RST.TyCodata loc _ xtors) =
    CST.TyXData loc CST.Codata (embedRST <$> xtors)
  embedRST (RST.TyDataRefined loc _ tn xtors) =
    CST.TyXRefined loc CST.Data (rnTnName tn) (embedRST <$> xtors)
  embedRST (RST.TyCodataRefined loc _ tn xtors) =
    CST.TyXRefined loc CST.Codata (rnTnName tn) (embedRST <$> xtors)
  embedRST (RST.TyNominal loc _ nm args) =
    CST.TyNominal loc (rnTnName nm) (embedRST args)
  embedRST (RST.TySyn loc _ nm _) =
    CST.TyNominal loc (rnTnName nm) []
  embedRST (RST.TyTop loc) =
    CST.TyTop loc
  embedRST (RST.TyBot loc) =
    CST.TyBot loc
  embedRST (RST.TyUnion loc ty ty') =
    CST.TyBinOp loc (embedRST ty) UnionOp (embedRST ty')
  embedRST (RST.TyInter loc ty ty') =
    CST.TyBinOp loc (embedRST ty) InterOp (embedRST ty')
  embedRST (RST.TyRec loc _ tv ty) =
    CST.TyRec loc (embedRecTVar tv) (embedRST ty)
  embedRST (RST.TyI64 loc _) =
    CST.TyI64 loc
  embedRST (RST.TyF64 loc _) =
    CST.TyF64 loc
  embedRST (RST.TyChar loc _) =
    CST.TyChar loc
  embedRST (RST.TyString loc _) =
    CST.TyString loc
  embedRST (RST.TyFlipPol _ ty) = embedRST ty

instance EmbedRST (RST.TypeScheme pol) CST.TypeScheme where
  embedRST :: RST.TypeScheme pol -> CST.TypeScheme
  embedRST RST.TypeScheme { ts_loc, ts_vars, ts_monotype } =
    CST.TypeScheme { ts_loc = ts_loc
                  , ts_vars = ts_vars
                  , ts_constraints = error "Type constraints not implemented yet for RST type scheme."
                  , ts_monotype = embedRST ts_monotype
                  }

---------------------------------------------------------------------------------
-- EmbedTST implementation for declarations
---------------------------------------------------------------------------------

instance EmbedRST RST.DataDecl CST.DataDecl where
  embedRST :: RST.DataDecl -> CST.DataDecl
  embedRST RST.NominalDecl { data_loc, data_doc, data_name, data_polarity, data_kind, data_xtors } =
    CST.MkDataDecl { data_loc = data_loc
                  , data_doc = data_doc
                  , data_refined = CST.NotRefined
                  , data_name = rnTnName data_name
                  , data_polarity = data_polarity
                  , data_kind = Just data_kind
                  , data_xtors = embedRST <$> fst data_xtors
                  }
  embedRST RST.RefinementDecl { data_loc, data_doc, data_name, data_polarity, data_kind, data_xtors } =
    CST.MkDataDecl { data_loc = data_loc
                  , data_doc = data_doc
                  , data_refined = CST.Refined
                  , data_name = rnTnName data_name
                  , data_polarity = data_polarity
                  , data_kind = Just data_kind
                  , data_xtors = embedRST <$> fst data_xtors
                  }

---------------------------------------------------------------------------------
-- CreateNames Monad
---------------------------------------------------------------------------------

reparseTerm :: RST.Term pc -> CST.Term
reparseTerm tm = embedRST (openTermComplete (evalState (createNames tm) names))

reparsePCTerm :: RST.PrdCnsTerm -> CST.Term
reparsePCTerm (RST.PrdTerm tm) = reparseTerm tm
reparsePCTerm (RST.CnsTerm tm) = reparseTerm tm

reparseSubst :: RST.Substitution -> CST.Substitution
reparseSubst = fmap reparsePCTerm

reparseSubstI :: RST.SubstitutionI pc -> CST.SubstitutionI
reparseSubstI (subst1,_,subst2) =
  (CST.ToSTerm <$> reparseSubst subst1) ++ [CST.ToSStar] ++ (CST.ToSTerm <$> reparseSubst subst2)

reparseCommand :: RST.Command -> CST.Term
reparseCommand cmd =
  embedRST (openCommandComplete (evalState (createNames cmd) names))

reparseCmdCase :: RST.CmdCase -> CST.TermCase
reparseCmdCase cmdcase =
  embedRST (evalState (createNames cmdcase) names)

reparseTermCase :: RST.TermCase pc -> CST.TermCase
reparseTermCase termcase =
  embedRST (evalState (createNames termcase) names)

reparseTermCaseI :: RST.TermCaseI pc -> CST.TermCase
reparseTermCaseI termcasei =
  embedRST (evalState (createNames termcasei) names)

reparseInstanceCase :: RST.InstanceCase -> CST.TermCase
reparseInstanceCase instancecase =
  embedRST (openInstanceCase (evalState (createNames instancecase) names))


reparsePrdCnsDeclaration :: RST.PrdCnsDeclaration pc -> CST.PrdCnsDeclaration
reparsePrdCnsDeclaration RST.MkPrdCnsDeclaration { pcdecl_loc, pcdecl_doc, pcdecl_pc, pcdecl_isRec, pcdecl_name, pcdecl_annot, pcdecl_term } =
  CST.MkPrdCnsDeclaration { pcdecl_loc = pcdecl_loc
                          , pcdecl_doc = pcdecl_doc
                          , pcdecl_pc = case pcdecl_pc of { PrdRep -> Prd; CnsRep -> Cns }
                          , pcdecl_isRec = pcdecl_isRec
                          , pcdecl_name = pcdecl_name
                          , pcdecl_annot = embedRST <$> pcdecl_annot
                          , pcdecl_term = reparseTerm pcdecl_term
                          }

reparseCommandDeclaration :: RST.CommandDeclaration -> CST.CommandDeclaration
reparseCommandDeclaration RST.MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd } =
  CST.MkCommandDeclaration { cmddecl_loc = cmddecl_loc
                           , cmddecl_doc = cmddecl_doc
                           , cmddecl_name = cmddecl_name
                           , cmddecl_cmd= reparseCommand cmddecl_cmd
                           }

reparseStructuralXtorDeclaration :: RST.StructuralXtorDeclaration -> CST.StructuralXtorDeclaration
reparseStructuralXtorDeclaration RST.MkStructuralXtorDeclaration { strxtordecl_loc, strxtordecl_doc, strxtordecl_xdata, strxtordecl_name, strxtordecl_arity, strxtordecl_evalOrder} =
  CST.MkStructuralXtorDeclaration { strxtordecl_loc = strxtordecl_loc
                                  , strxtordecl_doc = strxtordecl_doc
                                  , strxtordecl_xdata = strxtordecl_xdata
                                  , strxtordecl_name = strxtordecl_name
                                  , strxtordecl_arity= strxtordecl_arity
                                  , strxtordecl_evalOrder = Just strxtordecl_evalOrder
                                  }

reparseTySynDeclaration :: RST.TySynDeclaration -> CST.TySynDeclaration
reparseTySynDeclaration RST.MkTySynDeclaration { tysyndecl_loc, tysyndecl_doc, tysyndecl_name, tysyndecl_res } =
  CST.MkTySynDeclaration { tysyndecl_loc = tysyndecl_loc
                         , tysyndecl_doc = tysyndecl_doc
                         , tysyndecl_name = tysyndecl_name
                         , tysyndecl_res = embedRST (fst tysyndecl_res)
                         }

reparseTyOpDecl :: RST.TyOpDeclaration -> CST.TyOpDeclaration
reparseTyOpDecl RST.MkTyOpDeclaration { tyopdecl_loc, tyopdecl_doc, tyopdecl_sym, tyopdecl_prec, tyopdecl_assoc, tyopdecl_res } =
  CST.MkTyOpDeclaration { tyopdecl_loc = tyopdecl_loc
                        , tyopdecl_doc = tyopdecl_doc
                        , tyopdecl_sym = tyopdecl_sym
                        , tyopdecl_prec = tyopdecl_prec
                        , tyopdecl_assoc = tyopdecl_assoc
                        , tyopdecl_res = rnTnName tyopdecl_res
                        }

reparseClassDecl :: RST.ClassDeclaration -> CST.ClassDeclaration
reparseClassDecl RST.MkClassDeclaration { classdecl_loc, classdecl_doc, classdecl_name, classdecl_kinds, classdecl_methods }
  = CST.MkClassDeclaration { classdecl_loc     = classdecl_loc
                           , classdecl_doc     = classdecl_doc
                           , classdecl_name    = classdecl_name
                           , classdecl_kinds   = classdecl_kinds
                           , classdecl_methods = embedRST <$> fst classdecl_methods
                           }

reparseInstanceDecl :: RST.InstanceDeclaration -> CST.InstanceDeclaration
reparseInstanceDecl RST.MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_name, instancedecl_typ, instancedecl_cases }
  = CST.MkInstanceDeclaration { instancedecl_loc   = instancedecl_loc
                              , instancedecl_doc   = instancedecl_doc
                              , instancedecl_name  = instancedecl_name
                              , instancedecl_typ   = embedRST (fst instancedecl_typ)
                              , instancedecl_cases = reparseInstanceCase <$> instancedecl_cases
                              }

reparseDecl :: RST.Declaration -> CST.Declaration
reparseDecl (RST.PrdCnsDecl _ decl) =
  CST.PrdCnsDecl (reparsePrdCnsDeclaration decl)
reparseDecl (RST.CmdDecl decl) =
  CST.CmdDecl (reparseCommandDeclaration decl)
reparseDecl (RST.DataDecl decl) =
  CST.DataDecl (embedRST decl)
reparseDecl (RST.XtorDecl decl) =
  CST.XtorDecl (reparseStructuralXtorDeclaration decl)
reparseDecl (RST.ImportDecl decl) =
  CST.ImportDecl decl
reparseDecl (RST.SetDecl decl) =
  CST.SetDecl decl
reparseDecl (RST.TyOpDecl decl) =
  CST.TyOpDecl (reparseTyOpDecl decl)
reparseDecl (RST.TySynDecl decl) =
  CST.TySynDecl (reparseTySynDeclaration decl)
reparseDecl (RST.ClassDecl decl) =
  CST.ClassDecl (reparseClassDecl decl)
reparseDecl (RST.InstanceDecl decl) =
  CST.InstanceDecl (reparseInstanceDecl decl)

reparseModule :: RST.Module -> CST.Module
reparseModule RST.MkModule { mod_name, mod_fp, mod_decls } =
  CST.MkModule { mod_name = mod_name
               , mod_fp = mod_fp
               , mod_decls = reparseDecl <$> mod_decls
               }
