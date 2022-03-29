module Parser.Common
  ( -- Names
    freeVarNameP
  , tvarP
  , xtorNameP
  , typeNameP
  , moduleNameP
    -- Type Operators
  , tyOpNameP
  , tyBinOpP
  , precedenceP
  , associativityP
    -- Kinds
  , evalOrderP
  , monoKindP
  , polyKindP
  ) where

import Control.Monad (void)
import Text.Megaparsec

import Parser.Definition
import Parser.Lexer
import Syntax.Common

---------------------------------------------------------------------------------
-- Names
---------------------------------------------------------------------------------

freeVarNameP :: Parser (FreeVarName, SourcePos)
freeVarNameP = try $ do
  (name, pos) <- lowerCaseId
  return (MkFreeVarName name, pos)

tvarP :: Parser (TVar, SourcePos)
tvarP = try $ do
  (name, pos) <- lowerCaseId
  return (MkTVar name, pos)

xtorNameP :: Parser (XtorName, SourcePos)
xtorNameP = try $ do
  (name, pos) <- upperCaseId
  return (MkXtorName name, pos)

typeNameP :: Parser (TypeName, SourcePos)
typeNameP = try $ do
  (name, pos) <- upperCaseId
  return (MkTypeName name, pos)

moduleNameP :: Parser (ModuleName, SourcePos)
moduleNameP = try $ do
  (name, pos) <- upperCaseId
  return (MkModuleName name, pos)

---------------------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------------------

tyOpNameP :: Parser (TyOpName, SourcePos)
tyOpNameP = try $ do
  (name, pos) <- operatorP
  return (MkTyOpName name, pos)

tyBinOpP :: Parser BinOp
tyBinOpP = try (interOp <|> unionOp <|> customOp)
  where
    interOp  = InterOp <$ symbolP SymIntersection
    unionOp  = UnionOp <$ symbolP SymUnion
    customOp = tyOpNameP >>= (\(op,_) -> pure (CustomOp op))

precedenceP :: Parser Precedence
precedenceP = do
  (n,_) <- natP
  pure (MkPrecedence n)

associativityP :: Parser Associativity
associativityP = (keywordP KwLeftAssoc >> pure LeftAssoc) <|>
                 (keywordP KwRightAssoc >> pure RightAssoc)


---------------------------------------------------------------------------------
-- EvaluationOrder and MonoKinds
---------------------------------------------------------------------------------

evalOrderP :: Parser EvaluationOrder
evalOrderP = (keywordP KwCBV *> pure CBV) <|> (keywordP KwCBN *> pure CBN)

-- | Parses one of the keywords "CBV" or "CBN"
monoKindP :: Parser MonoKind
monoKindP = CBox <$> evalOrderP
         <|> CRep I64 <$ keywordP KwI64Rep
         <|> CRep F64 <$ keywordP KwF64Rep

---------------------------------------------------------------------------------
-- PolyKinds
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