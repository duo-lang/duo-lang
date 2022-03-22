module Parser.Types
  ( -- Kind Parser
    kindP
  , callingConventionP
  , evalOrderP
    -- Type Parsers
  , typeSchemeP
  , typP
  , typAtomP
  ) where

import Control.Monad.State
import Control.Monad.Reader ( asks, MonadReader(local) )
import Data.Set qualified as S
import Text.Megaparsec hiding (State)
import Data.List.NonEmpty (NonEmpty((:|)))

import Parser.Definition
import Parser.Lexer
import Syntax.Common
import Syntax.CST.Types
import Syntax.Primitives

---------------------------------------------------------------------------------
-- Parsing of Kinds
---------------------------------------------------------------------------------

-- | Parses one of the keywords "CBV" or "CBN"
callingConventionP :: Parser CallingConvention
callingConventionP = CBox <$> evalOrderP
                 <|> CRep I64 <$ i64RepKwP
                 <|> CRep F64 <$ f64RepKwP

-- | Parses a MonoKind, either "CBV" or "CBN"
kindP :: Parser Kind
kindP = MonoKind <$> callingConventionP

evalOrderP :: Parser EvaluationOrder
evalOrderP = (cbvKwP *> pure CBV) <|> (cbnKwP *> pure CBN)

---------------------------------------------------------------------------------
-- Parsing of linear contexts
---------------------------------------------------------------------------------

-- | Parse a parenthesized list of producer types.
-- E.g.: "(Nat, Bool, { Ap(Nat)[Bool] })"
prdCtxtPartP :: Parser LinearContext
prdCtxtPartP = do
  (res, _) <- parens $ (PrdType <$> typP) `sepBy` comma
  return res

-- | Parse a bracketed list of consumer types.
-- E.g.: "[Nat, Bool, { Ap(Nat)[Bool] }]"
cnsCtxtPartP :: Parser LinearContext
cnsCtxtPartP = do
  (res,_) <- brackets $ (CnsType <$> typP) `sepBy` comma
  return res

-- | Parse a linear context.
-- E.g.: "(Nat,Bool)[Int](Int)[Bool,Float]"
linearContextP :: Parser LinearContext
linearContextP = Prelude.concat <$> many (prdCtxtPartP <|> cnsCtxtPartP)

---------------------------------------------------------------------------------
-- Nominal and Structural Types
---------------------------------------------------------------------------------

nominalTypeArgsP :: Parser [Typ]
nominalTypeArgsP = (fst <$> parens (typP `sepBy` comma)) <|> pure []

-- | Parse a nominal type.
-- E.g. "Nat"
nominalTypeP :: Parser Typ
nominalTypeP = do
  (name, _pos) <- typeNameP
  TyNominal name <$> nominalTypeArgsP

-- | Parse a data or codata type. E.g.:
-- - "< ctor1 | ctor2 | ctor3 >"
-- - "{ dtor1 , dtor2 , dtor3 }"
xdataTypeP :: DataCodata -> Parser Typ
xdataTypeP Data = fst <$> angles (do
  xtorSigs <- xtorSignatureP `sepBy` comma
  return (TyXData Data Nothing xtorSigs))
xdataTypeP Codata = fst <$> braces (do
  xtorSigs <- xtorSignatureP `sepBy` comma
  return (TyXData Codata Nothing xtorSigs))

-- | Parse a Constructor or destructor signature. E.g.
-- - "Cons(Nat,List)"
-- - "Head[Nat]"
xtorSignatureP :: Parser XtorSig
xtorSignatureP = do
  (xt, _pos) <- xtorName
  MkXtorSig xt <$> linearContextP

---------------------------------------------------------------------------------
-- Type variables and recursive types
---------------------------------------------------------------------------------

-- | Parses a typevariable, and checks whether the typevariable is bound.
typeVariableP :: Parser Typ
typeVariableP = do
  tvs <- asks tvars
  (tvar, _) <- tvarP
  guard (tvar `S.member` tvs)
  return $ TyVar tvar

recTypeP :: Parser Typ
recTypeP = do
  _ <- recKwP
  (rv,_) <- tvarP
  _ <- dot
  ty <- local (\tpr@ParseReader{ tvars } -> tpr { tvars = S.insert rv tvars }) typP
  return $ TyRec rv ty

---------------------------------------------------------------------------------
-- Refinement types
---------------------------------------------------------------------------------

refinementTypeP :: DataCodata -> Parser Typ
refinementTypeP Data = fst <$> angles (do
  (tn,_) <- typeNameP
  _ <- pipe
  ctors <- xtorSignatureP `sepBy` comma
  pure $ TyXData Data (Just tn) ctors)
refinementTypeP Codata = fst <$> braces (do
  (tn,_) <- typeNameP
  _ <- pipe
  dtors <- xtorSignatureP `sepBy` comma
  pure $ TyXData Codata (Just tn) dtors)

---------------------------------------------------------------------------------
-- Primitive types
---------------------------------------------------------------------------------

primitiveTypeP :: Parser PrimitiveType
primitiveTypeP =
      I64 <$ i64KwP
  <|> F64 <$ f64KwP

---------------------------------------------------------------------------------
-- Type Parser
---------------------------------------------------------------------------------

-- | Parse atomic types
typAtomP :: Parser Typ
typAtomP = (TyParens . fst <$> parens typP)
  <|> nominalTypeP
  <|> try (refinementTypeP Data)
  <|> try (refinementTypeP Codata)
  <|> xdataTypeP Data
  <|> xdataTypeP Codata
  <|> recTypeP
  <|> TyTop <$ topKwP
  <|> TyBot <$ botKwP
  <|> TyPrim <$> primitiveTypeP
  <|> typeVariableP

tyOpP :: Parser BinOp
tyOpP = FunOp <$ thinRightarrow
    <|> InterOp <$ intersectionSym
    <|> UnionOp <$ unionSym
    <|> ParOp <$ parSym

opsChainP' :: Parser a -> Parser b -> Parser [(b, a)]
opsChainP' p op = do
  let fst = try ((,) <$> op <*> p)
  let rest = opsChainP' p op
  ((:) <$> fst <*> rest) <|> pure []

opsChainP :: Parser a -> Parser b -> Parser (a, NonEmpty (b, a))
opsChainP p op = do
  (fst, (o, snd)) <- try (((,) <$> p) <*> (((,) <$> op) <*> p))
  rest <- opsChainP' p op
  pure (fst, (o, snd) :| rest)

-- | Parse a chain of type operators
typOpsP :: Parser Typ
typOpsP = uncurry TyBinOpChain <$> opsChainP typAtomP tyOpP

-- | Parse a type
typP :: Parser Typ
typP = typOpsP <|> typAtomP


---------------------------------------------------------------------------------
-- Parsing of type schemes.
---------------------------------------------------------------------------------

-- | Parse a type scheme
typeSchemeP :: Parser TypeScheme
typeSchemeP = do
  tvars' <- option [] (forallKwP >> some (fst <$> tvarP) <* dot)
  monotype <- local (\s -> s { tvars = S.fromList tvars' }) typP
  pure (TypeScheme tvars' monotype)
