module Parser.Types
  ( -- Kind Parser
    monoKindP
  , polyKindP
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

---------------------------------------------------------------------------------
-- Parsing of Kinds
---------------------------------------------------------------------------------

-- | Parses one of the keywords "CBV" or "CBN"
monoKindP :: Parser MonoKind
monoKindP = CBox <$> evalOrderP
         <|> CRep I64 <$ keywordP KwI64Rep
         <|> CRep F64 <$ keywordP KwF64Rep


evalOrderP :: Parser EvaluationOrder
evalOrderP = (keywordP KwCBV *> pure CBV) <|> (keywordP KwCBN *> pure CBN)

---------------------------------------------------------------------------------
-- Parsing of PolyKinds
---------------------------------------------------------------------------------

varianceP :: Variance -> Parser ()
varianceP Covariant = void (symbolP SymPlus)
varianceP Contravariant = void (symbolP SymMinus)


polyKindP :: Parser PolyKind
polyKindP = f <|> g
  where
    f = do
      eo <- evalOrderP
      pure (MkPolyKind [] [] eo)
    g = do
      (contra, cov) <- tparamsP
      _ <- symbolP SymSimpleRightArrow
      ret <- evalOrderP
      pure (MkPolyKind contra cov ret)

tParamP :: Variance -> Parser (TVar, MonoKind)
tParamP v = do
  _ <- varianceP v
  (tvar,_) <- tvarP
  _ <- symbolP SymColon
  kind <- monoKindP
  pure (tvar, kind)

tparamsP :: Parser ([(TVar, MonoKind)],[(TVar, MonoKind)])
tparamsP =
  (fst <$> parens inner) <|> pure ([],[])
  where
    inner = do
      con_ps <- tParamP Contravariant `sepBy` try (symbolP SymComma <* notFollowedBy (varianceP Covariant))
      if null con_ps then
        (\x -> ([], x)) <$> tParamP Covariant `sepBy` symbolP SymComma
      else do
        cov_ps <-
          try (symbolP SymComma) *> tParamP Covariant `sepBy` symbolP SymComma
          <|> pure []
        pure (con_ps, cov_ps)

---------------------------------------------------------------------------------
-- Parsing of linear contexts
---------------------------------------------------------------------------------

-- | Parse a parenthesized list of producer types.
-- E.g.: "(Nat, Bool, { Ap(Nat)[Bool] })"
prdCtxtPartP :: Parser LinearContext
prdCtxtPartP = do
  (res, _) <- parens $ (PrdType <$> typP) `sepBy` symbolP SymComma
  return res

-- | Parse a bracketed list of consumer types.
-- E.g.: "[Nat, Bool, { Ap(Nat)[Bool] }]"
cnsCtxtPartP :: Parser LinearContext
cnsCtxtPartP = do
  (res,_) <- brackets $ (CnsType <$> typP) `sepBy` symbolP SymComma
  return res

-- | Parse a linear context.
-- E.g.: "(Nat,Bool)[Int](Int)[Bool,Float]"
linearContextP :: Parser LinearContext
linearContextP = Prelude.concat <$> many (prdCtxtPartP <|> cnsCtxtPartP)

---------------------------------------------------------------------------------
-- Nominal and Structural Types
---------------------------------------------------------------------------------

nominalTypeArgsP :: Parser [Typ]
nominalTypeArgsP = (fst <$> parens (typP `sepBy` symbolP SymComma)) <|> pure []

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
  xtorSigs <- xtorSignatureP `sepBy` symbolP SymComma
  return (TyXData Data Nothing xtorSigs))
xdataTypeP Codata = fst <$> braces (do
  xtorSigs <- xtorSignatureP `sepBy` symbolP SymComma
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
  _ <- keywordP KwRec
  (rv,_) <- tvarP
  _ <- symbolP SymDot
  ty <- local (\tpr@ParseReader{ tvars } -> tpr { tvars = S.insert rv tvars }) typP
  return $ TyRec rv ty

---------------------------------------------------------------------------------
-- Refinement types
---------------------------------------------------------------------------------

refinementTypeP :: DataCodata -> Parser Typ
refinementTypeP Data = fst <$> angles (do
  (tn,_) <- typeNameP
  _ <- symbolP SymPipe
  ctors <- xtorSignatureP `sepBy` symbolP SymComma
  pure $ TyXData Data (Just tn) ctors)
refinementTypeP Codata = fst <$> braces (do
  (tn,_) <- typeNameP
  _ <- symbolP SymPipe
  dtors <- xtorSignatureP `sepBy` symbolP SymComma
  pure $ TyXData Codata (Just tn) dtors)

---------------------------------------------------------------------------------
-- Primitive types
---------------------------------------------------------------------------------

primitiveTypeP :: Parser PrimitiveType
primitiveTypeP =
      I64 <$ keywordP KwI64 
  <|> F64 <$ keywordP KwF64

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
  <|> TyTop <$ keywordP KwTop
  <|> TyBot <$ keywordP KwBot
  <|> TyPrim <$> primitiveTypeP
  <|> typeVariableP

tyOpP :: Parser BinOp
tyOpP = interOp <|> unionOp <|> customOp
  where
    interOp  = InterOp <$ symbolP SymIntersection
    unionOp  = UnionOp <$ symbolP SymUnion
    customOp = tyOpNameP >>= (\(op,_) -> pure (CustomOp op))

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
  tvars' <- option [] (keywordP KwForall >> some (fst <$> tvarP) <* symbolP SymDot)
  monotype <- local (\s -> s { tvars = S.fromList tvars' }) typP
  pure (TypeScheme tvars' monotype)
