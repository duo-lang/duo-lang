module Syntax.Lowering.Program where

import Data.Bifunctor (first)
import Data.Text (Text)    
import Data.Text qualified as T

import Syntax.Lowering.Terms (lowerTerm, lowerCommand)
import Syntax.Lowering.Types (lowerTypeScheme, lowerXTorSig)
import Syntax.CST.Program qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.AST.Program qualified as AST
import Syntax.AST.Types qualified as AST
import Syntax.CommonTerm



lowerXtors :: [CST.XtorSig] -> Either Text ([AST.XtorSig AST.Pos], [AST.XtorSig AST.Neg])
lowerXtors sigs = do
    posSigs <- sequence $ first (T.pack . show) <$> lowerXTorSig AST.PosRep <$> sigs
    negSigs <- sequence $ first (T.pack . show) <$> lowerXTorSig AST.NegRep <$> sigs
    pure (posSigs, negSigs)

lowerDataDecl :: CST.DataDecl -> Either Text AST.DataDecl
lowerDataDecl CST.NominalDecl { data_name, data_polarity, data_kind, data_xtors } = do
    xtors <- lowerXtors data_xtors
    pure AST.NominalDecl { data_name = data_name
                         , data_polarity = data_polarity
                         , data_kind = data_kind
                         , data_xtors = xtors
                         }


lowerAnnot :: PrdCnsRep pc -> CST.TypeScheme -> Either Text (AST.TypeScheme (AST.PrdCnsToPol pc))
lowerAnnot PrdRep ts = first (T.pack . show) $ lowerTypeScheme AST.PosRep ts 
lowerAnnot CnsRep ts = first (T.pack . show) $ lowerTypeScheme AST.NegRep ts

lowerMaybeAnnot :: PrdCnsRep pc -> Maybe (CST.TypeScheme) -> Either Text (Maybe (AST.TypeScheme (AST.PrdCnsToPol pc)))
lowerMaybeAnnot _ Nothing = Right Nothing
lowerMaybeAnnot pc (Just annot) = Just <$> lowerAnnot pc annot

lowerDecl :: CST.Declaration -> Either Text (AST.Declaration Parsed)
lowerDecl (CST.PrdCnsDecl loc Prd isrec fv annot tm) = AST.PrdCnsDecl loc PrdRep isrec fv <$> (lowerMaybeAnnot PrdRep annot) <*> (lowerTerm PrdRep tm)
lowerDecl (CST.PrdCnsDecl loc Cns isrec fv annot tm) = AST.PrdCnsDecl loc CnsRep isrec fv <$> (lowerMaybeAnnot CnsRep annot) <*> (lowerTerm CnsRep tm)
lowerDecl (CST.CmdDecl loc fv cmd) = AST.CmdDecl loc fv <$> (lowerCommand cmd)
lowerDecl (CST.DataDecl loc dd)    = AST.DataDecl loc <$> lowerDataDecl dd
lowerDecl (CST.ImportDecl loc mod) = pure $ AST.ImportDecl loc mod
lowerDecl (CST.SetDecl loc txt)    = pure $ AST.SetDecl loc txt
lowerDecl (CST.FixityDecl loc assoc prec) = pure $ AST.FixityDecl loc assoc prec
lowerDecl CST.ParseErrorDecl       = Left "Unreachable: ParseErrorDecl cannot be parsed"

lowerProgram :: CST.Program -> Either Text (AST.Program Parsed)
lowerProgram = sequence . fmap lowerDecl
