module Parser.Types
  ( typeSchemeP
  , simpleTypeP
  ) where

import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Set as S
import Text.Megaparsec hiding (State)

import Parser.Definition
import Parser.Lexer
import Syntax.Terms
import Syntax.Types

---------------------------------------------------------------------------------
-- Parsing of Simple and Target types
---------------------------------------------------------------------------------

nominalTypeP :: Parser (Typ st)
nominalTypeP = TyNominal <$> typeNameP

dataTypeP :: SimpleTargetRep st -> Parser (Typ st)
dataTypeP rep = angles $ do
  xtorSigs <- xtorSignatureP rep `sepBy` pipe
  return (TySimple Data xtorSigs)

codataTypeP :: SimpleTargetRep st -> Parser (Typ st)
codataTypeP rep = braces $ do
  xtorSigs <- xtorSignatureP rep `sepBy` comma
  return (TySimple Codata xtorSigs)

xtorSignatureP :: SimpleTargetRep st -> Parser (XtorSig (Typ st))
xtorSignatureP rep = do
  xt <- xtorName Structural
  args <- argListP (lexeme (typP rep)) (lexeme (typP rep))
  return (MkXtorSig xt args)

recVar :: Parser TargetType
recVar = do
  rvs <- asks rvars
  rv <- MkTVar <$> freeVarName
  guard (rv `S.member` rvs)
  return $ TyVar Recursive rv

typeVariable :: Parser TargetType
typeVariable = do
  tvs <- asks tvars
  tv <- MkTVar <$> freeVarName
  guard (tv `S.member` tvs)
  return $ TyVar Normal tv

setType :: UnionInter -> Parser TargetType
setType Union = TySet () Union <$> (lexeme targetTypeP' `sepBy2` (symbol "\\/"))
setType Inter = TySet () Inter <$> (lexeme targetTypeP' `sepBy2` (symbol "/\\"))

recType :: Parser TargetType
recType = do
  _ <- symbol "rec"
  rv <- MkTVar <$> freeVarName
  _ <- dot
  ty <- local (\tpr@ParseReader{ rvars } -> tpr { rvars = S.insert rv rvars }) targetTypeP
  return $ TyRec () rv ty

-- Without joins and meets
targetTypeP' :: Parser TargetType
targetTypeP' = try (parens targetTypeP) <|>
  nominalTypeP <|>
  dataTypeP TargetRep <|>
  codataTypeP TargetRep <|>
  try recVar <|>
  recType <|>
  typeVariable

targetTypeP :: Parser TargetType
targetTypeP = try (setType Union) <|> try (setType Inter) <|> targetTypeP'

simpleTypeP :: Parser SimpleType
simpleTypeP = nominalTypeP <|> dataTypeP SimpleRep <|> codataTypeP SimpleRep

typP :: SimpleTargetRep st -> Parser (Typ st)
typP SimpleRep = simpleTypeP
typP TargetRep = targetTypeP

---------------------------------------------------------------------------------
-- Parsing of type schemes.
---------------------------------------------------------------------------------

typeSchemeP :: Parser TypeScheme
typeSchemeP = do
  tvars' <- S.fromList <$> option [] (symbol "forall" >> some (MkTVar <$> freeVarName) <* dot)
  monotype <- local (\s -> s { tvars = tvars' }) targetTypeP
  if tvars' == S.fromList (freeTypeVars monotype)
    then return (generalize monotype)
    else fail "Forall annotation in type scheme is incorrect"

