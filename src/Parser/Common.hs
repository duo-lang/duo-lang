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
  , methodNameP
  ) where

import Data.Functor ( ($>) )
import Text.Megaparsec

import Parser.Definition
import Parser.Lexer
import Syntax.Common.Names
import Syntax.CST.Kinds
import Syntax.Common.Primitives


---------------------------------------------------------------------------------
-- Names
---------------------------------------------------------------------------------

freeVarNameP :: Parser (FreeVarName, SourcePos)
freeVarNameP = try $ do
  (name, pos) <- lowerCaseIdL
  sc
  return (MkFreeVarName name, pos)

tvarP :: Parser (SkolemTVar, SourcePos)
tvarP = try $ do
  (name, pos) <- lowerCaseIdL
  sc
  return (MkSkolemTVar name, pos)


xtorNameP :: Parser (XtorName, SourcePos)
xtorNameP = try $ do
  (name, pos) <- upperCaseIdL
  sc
  return (MkXtorName name, pos)

typeNameP :: Parser (TypeName, SourcePos)
typeNameP = try $ do
  (name, pos) <- upperCaseIdL
  sc
  return (MkTypeName name, pos)

moduleNameP :: Parser (ModuleName, SourcePos)
moduleNameP = try $ do
  (name, pos) <- upperCaseIdL
  sc
  return (MkModuleName name, pos)

classNameP :: Parser (ClassName, SourcePos)
classNameP = try $ do
  (name, pos) <- upperCaseIdL
  sc
  return (MkClassName name, pos)

methodNameP :: Parser (MethodName, SourcePos)
methodNameP = try $ do
  (name, pos) <- upperCaseIdL
  sc
  return (MkMethodName name, pos)

---------------------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------------------

tyOpNameP :: Parser (TyOpName, SourcePos)
tyOpNameP = try $ do
  (name, pos) <- operatorP
  sc
  return (MkTyOpName name, pos)

tyBinOpP :: Parser (BinOp, SourcePos)
tyBinOpP = try (interOp <|> unionOp <|> customOp)
  where
    interOp  = do
      symbolP SymIntersection
      pos <- getSourcePos
      sc
      pure (InterOp, pos)
    unionOp  = do
      symbolP SymUnion
      pos <- getSourcePos
      sc
      pure (UnionOp, pos)
    customOp = do
      (op, pos) <- tyOpNameP
      pure (CustomOp op, pos)

precedenceP :: Parser Precedence
precedenceP = do
  (n,_) <- natP
  sc
  pure (MkPrecedence n)

associativityP :: Parser Associativity
associativityP = (keywordP KwLeftAssoc  >> sc >> pure LeftAssoc) <|>
                 (keywordP KwRightAssoc >> sc >> pure RightAssoc)


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
