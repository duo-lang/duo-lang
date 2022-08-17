module Parser.Common
  ( -- Names
    freeVarNameP
  , tvarP
  , xtorNameP
  , typeNameP
  , moduleNameP
  , classNameP
  , methodNameP
    -- Type Operators
  , tyOpNameP
  , tyBinOpP
  ) where

import Text.Megaparsec

import Parser.Definition
import Parser.Lexer
import Syntax.Common.Names


---------------------------------------------------------------------------------
-- Names
---------------------------------------------------------------------------------

freeVarNameP :: Parser (FreeVarName, SourcePos)
freeVarNameP = try $ do
  (name, pos) <- lowerCaseIdL
  return (MkFreeVarName name, pos)

tvarP :: Parser (SkolemTVar, SourcePos)
tvarP = try $ do
  (name, pos) <- lowerCaseIdL
  return (MkSkolemTVar name, pos)


xtorNameP :: Parser (XtorName, SourcePos)
xtorNameP = try $ do
  (name, pos) <- upperCaseIdL
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

