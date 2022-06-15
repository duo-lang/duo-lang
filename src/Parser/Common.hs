module Parser.Common
  ( -- Names
    freeVarNameP
  , tvarP
  , xtorNameP
  , typeNameP
  , moduleNameP
  , classNameP
    -- Type Operators
  , tyOpNameP
  , tyBinOpP
  , precedenceP
  , associativityP
  , tParamP
    -- Kinds
  , evalOrderP
  , monoKindP
  , polyKindP
  ,methodNameP) where

import Text.Megaparsec

import Parser.Definition
import Parser.Lexer
import Syntax.Common
import Data.Functor ( ($>) )

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

classNameP :: Parser (ClassName, SourcePos)
classNameP = try $ do
  (name, pos) <- upperCaseId
  return (MkClassName name, pos)

methodNameP :: Parser (MethodName, SourcePos)
methodNameP = try $ do
  (name, pos) <- upperCaseId
  return (MkMethodName name, pos)

---------------------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------------------

tyOpNameP :: Parser (TyOpName, SourcePos)
tyOpNameP = try $ do
  (name, pos) <- operatorP
  return (MkTyOpName name, pos)

tyBinOpP :: Parser (BinOp, SourcePos)
tyBinOpP = try (interOp <|> unionOp <|> customOp)
  where
    interOp  = symbolP SymIntersection >>= \pos -> pure (InterOp, pos)
    unionOp  = symbolP SymUnion >>= \pos -> pure (UnionOp, pos)
    customOp = tyOpNameP >>= (\(op,pos) -> pure (CustomOp op, pos))

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
evalOrderP = (keywordP KwCBV $> CBV) <|> (keywordP KwCBN $> CBN)

-- | Parses one of the keywords "CBV" or "CBN"
monoKindP :: Parser MonoKind
monoKindP = CBox <$> evalOrderP
         <|> CRep I64 <$ keywordP KwI64Rep
         <|> CRep F64 <$ keywordP KwF64Rep

---------------------------------------------------------------------------------
-- PolyKinds
---------------------------------------------------------------------------------

varianceP :: Parser Variance
varianceP = (symbolP SymPlus $> Covariant) <|> (symbolP SymMinus $> Contravariant)

polyKindP :: Parser PolyKind
polyKindP = f <|> g
  where
    f = MkPolyKind [] <$> evalOrderP
    g = do
      (kindArgs,_) <- parens (tParamP `sepBy` symbolP SymComma)
      _ <- symbolP SymSimpleRightArrow
      MkPolyKind kindArgs <$> evalOrderP

tParamP :: Parser (Variance, TVar, MonoKind)
tParamP = do
  v <- varianceP
  (tvar,_) <- tvarP
  _ <- symbolP SymColon
  kind <- monoKindP
  pure (v, tvar, kind)