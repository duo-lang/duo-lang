module Syntax.Lowering.Program (lowerProgram, lowerDecl) where

import Control.Monad.Except (throwError)

import Errors
import Syntax.Lowering.Terms (lowerTerm, lowerCommand)
import Syntax.Lowering.Types (lowerTypeScheme, lowerXTorSig)
import Syntax.Lowering.Lowering
import Syntax.CST.Program qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.AST.Program qualified as AST
import Syntax.AST.Types qualified as AST
import Syntax.CommonTerm



lowerXtors :: [CST.XtorSig] -> LowerM ([AST.XtorSig AST.Pos], [AST.XtorSig AST.Neg])
lowerXtors sigs = do
    posSigs <- sequence $ lowerXTorSig AST.PosRep <$> sigs
    negSigs <- sequence $ lowerXTorSig AST.NegRep <$> sigs
    pure (posSigs, negSigs)

lowerDataDecl :: CST.DataDecl -> LowerM AST.DataDecl
lowerDataDecl CST.NominalDecl { data_name, data_polarity, data_kind, data_xtors } = do
    xtors <- lowerXtors data_xtors
    pure AST.NominalDecl { data_name = data_name
                         , data_polarity = data_polarity
                         , data_kind = data_kind
                         , data_xtors = xtors
                         }


lowerAnnot :: PrdCnsRep pc -> CST.TypeScheme -> LowerM (AST.TypeScheme (AST.PrdCnsToPol pc))
lowerAnnot PrdRep ts = lowerTypeScheme AST.PosRep ts 
lowerAnnot CnsRep ts = lowerTypeScheme AST.NegRep ts

lowerMaybeAnnot :: PrdCnsRep pc -> Maybe (CST.TypeScheme) -> LowerM (Maybe (AST.TypeScheme (AST.PrdCnsToPol pc)))
lowerMaybeAnnot _ Nothing = pure Nothing
lowerMaybeAnnot pc (Just annot) = Just <$> lowerAnnot pc annot

lowerDecl :: CST.Declaration -> LowerM (AST.Declaration Parsed)
lowerDecl (CST.PrdCnsDecl loc Prd isrec fv annot tm) = AST.PrdCnsDecl loc PrdRep isrec fv <$> (lowerMaybeAnnot PrdRep annot) <*> (lowerTerm PrdRep tm)
lowerDecl (CST.PrdCnsDecl loc Cns isrec fv annot tm) = AST.PrdCnsDecl loc CnsRep isrec fv <$> (lowerMaybeAnnot CnsRep annot) <*> (lowerTerm CnsRep tm)
lowerDecl (CST.CmdDecl loc fv cmd) = AST.CmdDecl loc fv <$> (lowerCommand cmd)
lowerDecl (CST.DataDecl loc dd)    = AST.DataDecl loc <$> lowerDataDecl dd
lowerDecl (CST.ImportDecl loc mod) = pure $ AST.ImportDecl loc mod
lowerDecl (CST.SetDecl loc txt)    = pure $ AST.SetDecl loc txt
lowerDecl CST.ParseErrorDecl       = throwError (OtherError Nothing "Unreachable: ParseErrorDecl cannot be parsed")

lowerProgram :: CST.Program -> LowerM (AST.Program Parsed)
lowerProgram = sequence . fmap lowerDecl
