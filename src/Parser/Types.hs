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

typArgListP :: PolarityRep st -> Parser (TypArgs st)
typArgListP rep = do
  (Twice prdArgs cnsArgs) <- argListP (lexeme (typP rep)) (lexeme (typP rep))
  return (MkTypArgs prdArgs cnsArgs)

nominalTypeP :: Parser (Typ st)
nominalTypeP = TyNominal <$> typeNameP

dataTypeP :: PolarityRep st -> Parser (Typ st)
dataTypeP rep = angles $ do
  xtorSigs <- xtorSignatureP rep `sepBy` pipe
  return (TyStructural Data xtorSigs)

codataTypeP :: PolarityRep st -> Parser (Typ st)
codataTypeP rep = braces $ do
  xtorSigs <- xtorSignatureP rep `sepBy` comma
  return (TyStructural Codata xtorSigs)

xtorSignatureP :: PolarityRep st -> Parser (XtorSig st)
xtorSignatureP rep = do
  xt <- xtorName Structural
  args <- typArgListP rep
  return (MkXtorSig xt args)

recVar :: Parser (Typ st)
recVar = do
  rvs <- asks rvars
  rv <- MkTVar <$> freeVarName
  guard (rv `S.member` rvs)
  return $ TyVar Recursive rv

typeVariable :: Parser (Typ st)
typeVariable = do
  tvs <- asks tvars
  tv <- MkTVar <$> freeVarName
  guard (tv `S.member` tvs)
  return $ TyVar Normal tv

setType :: PolarityRep st -> UnionInter -> Parser (Typ st)
setType rep Union = TySet Union <$> (lexeme (typP' rep) `sepBy2` (symbol "\\/"))
setType rep Inter = TySet Inter <$> (lexeme (typP' rep) `sepBy2` (symbol "/\\"))

recType :: PolarityRep st -> Parser (Typ st)
recType rep = do
  _ <- symbol "rec"
  rv <- MkTVar <$> freeVarName
  _ <- dot
  ty <- local (\tpr@ParseReader{ rvars } -> tpr { rvars = S.insert rv rvars }) (typP rep)
  return $ TyRec rv ty

-- Without joins and meets
typP' :: PolarityRep st -> Parser (Typ st)
typP' rep = try (parens (typP rep)) <|>
  nominalTypeP <|>
  dataTypeP rep <|>
  codataTypeP rep <|>
  try recVar <|>
  recType rep <|>
  typeVariable

typP :: PolarityRep st -> Parser (Typ st)
typP rep = try (setType rep Union) <|> try (setType rep Inter) <|> typP' rep

---------------------------------------------------------------------------------
-- Parsing of type schemes.
---------------------------------------------------------------------------------

typeSchemeP :: Parser TypeScheme
typeSchemeP = do
  tvars' <- S.fromList <$> option [] (symbol "forall" >> some (MkTVar <$> freeVarName) <* dot)
  monotype <- local (\s -> s { tvars = tvars' }) (typP NegRep)
  if tvars' == S.fromList (freeTypeVars monotype)
    then return (generalize monotype)
    else fail "Forall annotation in type scheme is incorrect"

