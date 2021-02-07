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

---------------------------------------------------------------------------------
-- Parsing of Simple and Target types
---------------------------------------------------------------------------------

typArgListP :: PolarityRep pol -> Parser (TypArgs pol)
typArgListP rep = do
  prdArgs <- option [] (parens   $ (lexeme (typP rep)) `sepBy` comma)
  cnsArgs <- option [] (brackets $ (lexeme (typP (flipPolarityRep rep))) `sepBy` comma)
  return (MkTypArgs prdArgs cnsArgs)

nominalTypeP :: PolarityRep pol -> Parser (Typ pol)
nominalTypeP rep = TyNominal rep <$> typeNameP

dataTypeP :: PolarityRep pol -> Parser (Typ pol)
dataTypeP PosRep = angles $ do
  xtorSigs <- xtorSignatureP PosRep `sepBy` pipe
  return (TyStructural PosRep DataRep xtorSigs)
dataTypeP NegRep = angles $ do
  xtorSigs <- xtorSignatureP NegRep `sepBy` pipe
  return (TyStructural NegRep DataRep xtorSigs)

codataTypeP :: PolarityRep pol -> Parser (Typ pol)
codataTypeP PosRep = braces $ do
  xtorSigs <- xtorSignatureP NegRep `sepBy` comma
  return (TyStructural PosRep CodataRep xtorSigs)
codataTypeP NegRep = braces $ do
  xtorSigs <- xtorSignatureP PosRep `sepBy` comma
  return (TyStructural NegRep CodataRep xtorSigs)

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

setType :: PolarityRep pol -> Parser (Typ pol)
setType PosRep = TySet PosRep <$> (lexeme (typP' PosRep) `sepBy2` (symbol "\\/"))
setType NegRep = TySet NegRep <$> (lexeme (typP' NegRep) `sepBy2` (symbol "/\\"))

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
typP rep = try (setType rep) <|> typP' rep

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

