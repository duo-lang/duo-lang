module Parser.Kinds
  ( -- Kinds
    evalOrderP
  , monoKindP
  , polyKindP
  , tParamP
  ) where

import Text.Megaparsec

import Parser.Definition
import Parser.Lexer
import Parser.Names
import Syntax.CST.Kinds
import Syntax.CST.Names

---------------------------------------------------------------------------------
-- EvaluationOrder and MonoKinds
---------------------------------------------------------------------------------

evalOrderP :: Parser EvaluationOrder
evalOrderP = (keywordP KwCBV >> sc >> pure CBV) <|> 
             (keywordP KwCBN >> sc >> pure CBN)

-- | Parses one of the keywords "CBV" or "CBN"
monoKindP :: Parser MonoKind
monoKindP = CBox <$> evalOrderP
         <|> I64Rep <$ (keywordP KwI64Rep >> sc)
         <|> F64Rep <$ (keywordP KwF64Rep >> sc)
         <|> CharRep <$ (keywordP KwCharRep >> sc)
         <|> StringRep <$ (keywordP KwStringRep >> sc)

---------------------------------------------------------------------------------
-- PolyKinds
---------------------------------------------------------------------------------

varianceP :: Parser Variance
varianceP = variantP <|> covariantP
  where
    variantP = do
      symbolP SymPlus
      sc
      pure Covariant
    covariantP = do
      symbolP SymMinus
      sc
      pure Contravariant

polyKindP :: Parser PolyKind
polyKindP = f <|> g
  where
    f = MkPolyKind [] <$> evalOrderP
    g = do
      (kindArgs,_) <- parensP (tParamP `sepBy` (symbolP SymComma >> sc))
      sc
      symbolP SymSimpleRightArrow
      sc
      MkPolyKind kindArgs <$> evalOrderP

tParamP :: Parser (Variance, SkolemTVar, MonoKind)
tParamP = do
  v <- varianceP
  (tvar,_) <- tvarP
  sc
  symbolP SymColon
  sc
  kind <- monoKindP
  pure (v, tvar, kind)
