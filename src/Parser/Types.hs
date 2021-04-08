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
  prdArgs <- option [] (parens   $ (typP rep) `sepBy` comma)
  cnsArgs <- option [] (brackets $ (typP (flipPolarityRep rep)) `sepBy` comma)
  return (MkTypArgs prdArgs cnsArgs)

nominalTypeP :: PolarityRep pol -> Parser (Typ pol)
nominalTypeP rep = do
  (name, _pos) <- typeNameP
  pure $ TyNominal rep name

dataTypeP :: DataCodataRep dc -> PolarityRep pol -> Parser (Typ pol)
dataTypeP DataRep polrep = angles $ do
  xtorSigs <- xtorSignatureP polrep `sepBy` pipe
  return (TyData polrep xtorSigs)
dataTypeP CodataRep polrep = braces $ do
  xtorSigs <- xtorSignatureP (flipPolarityRep polrep) `sepBy` comma
  return (TyCodata polrep xtorSigs)

xtorSignatureP :: PolarityRep pol -> Parser (XtorSig pol)
xtorSignatureP PosRep = do
  (xt, _pos) <- xtorName Structural
  args <- typArgListP PosRep
  return (MkXtorSig xt args)
xtorSignatureP NegRep = do
  (xt, _pos) <- xtorName Structural
  args <- typArgListP NegRep
  return (MkXtorSig xt args)

typeVariable :: PolarityRep pol -> Parser (Typ pol)
typeVariable rep = do
  tvs <- asks tvars
  tv <- MkTVar . fst <$> freeVarName
  guard (tv `S.member` tvs)
  return $ TyVar rep tv

sepBy2 :: Parser a -> Parser sep -> Parser [a]
sepBy2 p sep = do
  fst <- p
  _ <- sep
  rest <- sepBy1 p sep
  return (fst : rest)

setType :: PolarityRep pol -> Parser (Typ pol)
setType PosRep = TySet PosRep <$> (typP' PosRep) `sepBy2` unionSym
setType NegRep = TySet NegRep <$> (typP' NegRep) `sepBy2` intersectionSym

recType :: PolarityRep pol -> Parser (Typ pol)
recType rep = do
  _ <- recKwP
  rv <- MkTVar . fst <$> freeVarName
  _ <- dot
  ty <- local (\tpr@ParseReader{ tvars } -> tpr { tvars = S.insert rv tvars }) (typP rep)
  return $ TyRec rep rv ty

-- Without joins and meets
typP' :: PolarityRep pol -> Parser (Typ pol)
typP' rep = try (parens (typP rep)) <|>
  nominalTypeP rep <|>
  dataTypeP DataRep rep <|>
  dataTypeP CodataRep rep <|>
  recType rep <|>
  typeVariable rep

typP :: PolarityRep pol -> Parser (Typ pol)
typP rep = try (setType rep) <|> typP' rep

---------------------------------------------------------------------------------
-- Parsing of type schemes.
---------------------------------------------------------------------------------

typeSchemeP :: Parser (TypeScheme 'Pos)
typeSchemeP = do
  tvars' <- S.fromList <$> option [] (forallKwP >> some (MkTVar . fst <$> freeVarName) <* dot)
  monotype <- local (\s -> s { tvars = tvars' }) (typP PosRep)
  if tvars' == S.fromList (freeTypeVars monotype)
    then return (generalize monotype)
    else fail "Forall annotation in type scheme is incorrect"

