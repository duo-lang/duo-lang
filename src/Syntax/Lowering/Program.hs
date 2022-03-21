module Syntax.Lowering.Program (lowerProgram, lowerDecl) where

import Control.Monad.Except
import Control.Monad.Reader

import Errors
import Syntax.Lowering.Terms (lowerTerm, lowerCommand)
import Syntax.Lowering.Types (lowerTypeScheme, lowerXTorSig)
import Syntax.CST.Program qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.AST.Program qualified as AST
import Syntax.AST.Types qualified as AST
import Syntax.Common
import Driver.SymbolTable (SymbolTable(..))
import Syntax.AST.Types (DataDecl(data_params))

type LowerM m = (MonadReader SymbolTable m, MonadError Error m)

lowerXtors :: LowerM m => [CST.XtorSig] -> m ([AST.XtorSig Pos], [AST.XtorSig Neg])
lowerXtors sigs = do
    posSigs <- sequence $ lowerXTorSig PosRep <$> sigs
    negSigs <- sequence $ lowerXTorSig NegRep <$> sigs
    pure (posSigs, negSigs)

lowerDataDecl :: LowerM m => CST.DataDecl -> m AST.DataDecl
lowerDataDecl CST.NominalDecl { data_refined, data_name, data_polarity, data_kind, data_xtors, data_params } = do
  xtors <- lowerXtors data_xtors
  pure AST.NominalDecl
        { data_refined = data_refined
        , data_name = data_name
        , data_polarity = data_polarity
        , data_kind = data_kind
        , data_xtors = xtors
        , data_params = data_params
        }

lowerAnnot :: LowerM m => PrdCnsRep pc -> CST.TypeScheme -> m (AST.TypeScheme (PrdCnsToPol pc))
lowerAnnot PrdRep ts = lowerTypeScheme PosRep ts
lowerAnnot CnsRep ts = lowerTypeScheme NegRep ts

lowerMaybeAnnot :: LowerM m => PrdCnsRep pc -> Maybe (CST.TypeScheme) -> m (Maybe (AST.TypeScheme (PrdCnsToPol pc)))
lowerMaybeAnnot _ Nothing = pure Nothing
lowerMaybeAnnot pc (Just annot) = Just <$> lowerAnnot pc annot

lowerDecl :: LowerM m => CST.Declaration -> m (AST.Declaration Parsed)
lowerDecl (CST.PrdCnsDecl loc Prd isrec fv annot tm) = AST.PrdCnsDecl loc PrdRep isrec fv <$> (lowerMaybeAnnot PrdRep annot) <*> (lowerTerm PrdRep tm)
lowerDecl (CST.PrdCnsDecl loc Cns isrec fv annot tm) = AST.PrdCnsDecl loc CnsRep isrec fv <$> (lowerMaybeAnnot CnsRep annot) <*> (lowerTerm CnsRep tm)
lowerDecl (CST.CmdDecl loc fv cmd)          = AST.CmdDecl loc fv <$> (lowerCommand cmd)
lowerDecl (CST.DataDecl loc tyDecl)             = do
  loweredDecl <- lowerDataDecl tyDecl
  pure $ AST.DataDecl loc loweredDecl
lowerDecl (CST.XtorDecl loc dc xt args ret) = do
  pure $ AST.XtorDecl loc dc xt args ret
lowerDecl (CST.ImportDecl loc mod) = do
  pure $ AST.ImportDecl loc mod
lowerDecl (CST.SetDecl loc txt)             = pure $ AST.SetDecl loc txt
lowerDecl CST.ParseErrorDecl                = throwError (OtherError Nothing "Unreachable: ParseErrorDecl cannot be parsed")

lowerProgram :: LowerM m => CST.Program -> m (AST.Program Parsed)
lowerProgram = sequence . fmap lowerDecl
