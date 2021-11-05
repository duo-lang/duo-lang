module Parser.Types
  ( -- Kind Parser
    kindP
    -- Type Parsers
  , typeSchemeP
  , typP
    -- Invariant Types
  , Invariant(..)
  , invariantP
  ) where

import Control.Monad.State
import Control.Monad.Reader
import Data.Set qualified as S
import Text.Megaparsec hiding (State)

import Parser.Definition
import Parser.Lexer
import Syntax.CommonTerm
import Syntax.Types
import Syntax.Kinds

---------------------------------------------------------------------------------
-- Parsing of Kinds
---------------------------------------------------------------------------------

evalOrderP :: Parser CallingConvention 
evalOrderP = cbvKwP *> return CBV <|> cbnKwP *> return CBN

kindP :: Parser Kind
kindP = do
  _ <- typeKwP
  eo <- evalOrderP
  return $ MonoKind eo


---------------------------------------------------------------------------------
-- Parsing of Simple and Target types
---------------------------------------------------------------------------------

typArgListP :: PolarityRep pol -> Parser (TypArgs pol)
typArgListP rep = do
  prdArgs <- option [] (fst <$> parens   (typP rep `sepBy` comma))
  cnsArgs <- option [] (fst <$> brackets (typP (flipPolarityRep rep) `sepBy` comma))
  return (MkTypArgs prdArgs cnsArgs)

nominalTypeP :: PolarityRep pol -> Parser (Typ pol)
nominalTypeP rep = do
  (name, _pos) <- typeNameP
  pure $ TyNominal rep Nothing name

dataTypeP :: DataCodataRep dc -> PolarityRep pol -> Parser (Typ pol)
dataTypeP DataRep polrep = fst <$> angles (do
  xtorSigs <- xtorSignatureP polrep `sepBy` pipe
  return (TyData polrep Nothing xtorSigs))
dataTypeP CodataRep polrep = fst <$> braces (do
  xtorSigs <- xtorSignatureP (flipPolarityRep polrep) `sepBy` comma
  return (TyCodata polrep Nothing xtorSigs))

xtorSignatureP :: PolarityRep pol -> Parser (XtorSig pol)
xtorSignatureP PosRep = do
  (xt, _pos) <- xtorName Structural <|> xtorName Nominal
  args <- typArgListP PosRep
  return (MkXtorSig xt args)
xtorSignatureP NegRep = do
  (xt, _pos) <- xtorName Structural <|> xtorName Nominal
  args <- typArgListP NegRep
  return (MkXtorSig xt args)

typeVariable :: PolarityRep pol -> Parser (Typ pol)
typeVariable rep = do
  tvs <- asks tvars
  tv <- MkTVar . fst <$> freeVarName
  guard (tv `S.member` tvs)
  return $ TyVar rep Nothing tv

sepBy2 :: Parser a -> Parser sep -> Parser [a]
sepBy2 p sep = do
  fst <- p
  _ <- sep
  rest <- sepBy1 p sep
  return (fst : rest)

setType :: PolarityRep pol -> Parser (Typ pol)
setType PosRep = botKwP *> return (TySet PosRep Nothing []) <|> TySet PosRep Nothing <$> (typP' PosRep) `sepBy2` unionSym
setType NegRep = topKwP *> return (TySet NegRep Nothing []) <|> TySet NegRep Nothing <$> (typP' NegRep) `sepBy2` intersectionSym

recType :: PolarityRep pol -> Parser (Typ pol)
recType rep = do
  _ <- recKwP
  rv <- MkTVar . fst <$> freeVarName
  _ <- dot
  ty <- local (\tpr@ParseReader{ tvars } -> tpr { tvars = S.insert rv tvars }) (typP rep)
  return $ TyRec rep rv ty

refTypeP :: PolarityRep pol -> Parser (Typ pol)
refTypeP rep = fst <$> dbraces (do
  (tn,_) <- typeNameP
  _ <- refineSym
  ty <- typP rep
  case ty of
    TyData _ Nothing ctors -> return $ TyData rep (Just tn) ctors
    TyCodata _ Nothing dtors -> return $ TyCodata rep (Just tn) dtors
    _ -> error "Second component of refinement type must be data or codata type"
  )

-- Without joins and meets
typP' :: PolarityRep pol -> Parser (Typ pol)
typP' rep = try (fst <$> parens (typP rep)) <|>
  nominalTypeP rep <|>
  refTypeP rep <|>
  dataTypeP DataRep rep <|>
  dataTypeP CodataRep rep <|>
  recType rep <|>
  typeVariable rep

typP :: PolarityRep pol -> Parser (Typ pol)
typP rep = try (setType rep) <|> typP' rep

---------------------------------------------------------------------------------
-- Parsing of invariant Types (HACKY!)
---------------------------------------------------------------------------------

newtype Invariant = MkInvariant { unInvariant :: forall pol. PolarityRep pol -> Typ pol }

-- DO NOT EXPORT! Hacky workaround.
switchPol :: Typ pol -> Typ (FlipPol pol)
switchPol (TyVar rep kind tv) = TyVar (flipPolarityRep rep) kind tv
switchPol (TyData rep mtn xtors) = TyData (flipPolarityRep rep) mtn (switchSig <$> xtors)
switchPol (TyCodata rep mtn xtors) = TyCodata (flipPolarityRep rep) mtn (switchSig <$> xtors)
switchPol (TyNominal rep kind tn) = TyNominal (flipPolarityRep rep) kind tn
switchPol (TySet rep kind typs) = TySet (flipPolarityRep rep) kind (switchPol <$> typs)
switchPol (TyRec rep tv typ) = TyRec (flipPolarityRep rep) tv (switchPol typ)

switchSig :: XtorSig pol -> XtorSig (FlipPol pol)
switchSig (MkXtorSig xt (MkTypArgs prdArgs cnsArgs)) = MkXtorSig xt (MkTypArgs (switchPol <$> prdArgs) (switchPol <$> cnsArgs))

invariantP :: Parser Invariant
invariantP = do
  typ <- typP' PosRep
  pure $ MkInvariant $ \rep -> case rep of PosRep -> typ ; NegRep -> switchPol typ


---------------------------------------------------------------------------------
-- Parsing of type schemes.
---------------------------------------------------------------------------------

typeSchemeP :: PolarityRep pol -> Parser (TypeScheme pol)
typeSchemeP polrep = do
  tvars' <- S.fromList <$> option [] (forallKwP >> some (MkTVar . fst <$> freeVarName) <* dot)
  monotype <- local (\s -> s { tvars = tvars' }) (typP polrep)
  if S.fromList (freeTypeVars monotype) `S.isSubsetOf` tvars'
    then return (TypeScheme (S.toList tvars') monotype)
    else fail "Forall annotation in type scheme is incorrect"

