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
import Parser.Common
import Syntax.Common.Names
import Syntax.Common.Primitives
import Syntax.CST.Kinds

---------------------------------------------------------------------------------
-- EvaluationOrder and MonoKinds
---------------------------------------------------------------------------------

evalOrderP :: Parser EvaluationOrder
evalOrderP = (keywordP KwCBV >> sc >> pure CBV) <|> 
             (keywordP KwCBN >> sc >> pure CBN)

-- | Parses one of the keywords "CBV" or "CBN"
monoKindP :: Parser MonoKind
monoKindP = CBox <$> evalOrderP
         <|> CRep I64 <$ (keywordP KwI64Rep >> sc)
         <|> CRep F64 <$ (keywordP KwF64Rep >> sc)
         <|> CRep PChar <$ (keywordP KwCharRep >> sc)
         <|> CRep PString <$ (keywordP KwStringRep >> sc)

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
  symbolP SymColon
  sc
  kind <- monoKindP
  pure (v, tvar, kind)
