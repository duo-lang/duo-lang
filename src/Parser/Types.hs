module Parser.Types
  ( typeSchemeP
  , typP
  , typArgListP
  ) where

import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Set as S
import Text.Megaparsec hiding (State)

import Parser.Definition
import Parser.Lexer
import Syntax.CommonTerm
import Syntax.Types
import Utils

---------------------------------------------------------------------------------
-- Parsing of Simple and Target types
---------------------------------------------------------------------------------

typArgListP :: PolarityRep pol -> Parser (TypArgs pol)
typArgListP rep = do
  (Twice prdArgs cnsArgs) <- argListP (lexeme (typP rep)) (lexeme (typP rep))
  return (MkTypArgs prdArgs cnsArgs)

nominalTypeP :: PolarityRep pol -> Parser (Typ pol)
nominalTypeP rep = TyNominal rep <$> typeNameP

dataTypeP :: PolarityRep pol -> Parser (Typ pol)
dataTypeP rep = angles $ do
  xtorSigs <- xtorSignatureP rep `sepBy` pipe
  return (TyStructural rep DataRep xtorSigs)

codataTypeP :: PolarityRep pol -> Parser (Typ pol)
codataTypeP rep = braces $ do
  xtorSigs <- xtorSignatureP rep `sepBy` comma
  return (TyStructural rep CodataRep xtorSigs)

xtorSignatureP :: PolarityRep pol -> Parser (XtorSig pol)
xtorSignatureP rep = do
  xt <- xtorName Structural
  args <- typArgListP rep
  return (MkXtorSig xt args)

recVar :: PolarityRep pol -> Parser (Typ pol)
recVar rep = do
  rvs <- asks rvars
  rv <- MkTVar <$> freeVarName
  guard (rv `S.member` rvs)
  return $ TyVar rep Recursive rv

typeVariable :: PolarityRep pol -> Parser (Typ pol)
typeVariable rep = do
  tvs <- asks tvars
  tv <- MkTVar <$> freeVarName
  guard (tv `S.member` tvs)
  return $ TyVar rep Normal tv

setType :: PolarityRep pol -> Polarity -> Parser (Typ pol)
setType rep Pos = TySet PosRep <$> (lexeme (typP' rep) `sepBy2` (symbol "\\/"))
setType rep Neg = TySet NegRep <$> (lexeme (typP' rep) `sepBy2` (symbol "/\\"))

recType :: PolarityRep pol -> Parser (Typ pol)
recType rep = do
  _ <- symbol "rec"
  rv <- MkTVar <$> freeVarName
  _ <- dot
  ty <- local (\tpr@ParseReader{ rvars } -> tpr { rvars = S.insert rv rvars }) (typP rep)
  return $ TyRec rep rv ty

-- Without joins and meets
typP' :: PolarityRep pol -> Parser (Typ pol)
typP' rep = try (parens (typP rep)) <|>
  nominalTypeP rep <|>
  dataTypeP rep <|>
  codataTypeP rep <|>
  try (recVar rep) <|>
  recType rep <|>
  typeVariable rep

typP :: PolarityRep pol -> Parser (Typ pol)
typP rep = try (setType rep Pos) <|> try (setType rep Neg) <|> typP' rep

---------------------------------------------------------------------------------
-- Parsing of type schemes.
---------------------------------------------------------------------------------

typeSchemeP :: Parser (TypeScheme 'Pos)
typeSchemeP = do
  tvars' <- S.fromList <$> option [] (symbol "forall" >> some (MkTVar <$> freeVarName) <* dot)
  monotype <- local (\s -> s { tvars = tvars' }) (typP PosRep)
  if tvars' == S.fromList (freeTypeVars monotype)
    then return (generalize monotype)
    else fail "Forall annotation in type scheme is incorrect"

