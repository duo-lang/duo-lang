module Parser.Common
  ( -- Names
    freeVarNameP
  , tvarP
  , primNameP
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

import Parser.Definition ( Parser )
import Parser.Lexer
import Syntax.CST.Names

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
  return (MkTypeName name, pos)

moduleNameP :: Parser (ModuleName, SourcePos)
moduleNameP = try $ do
  --  path <- many (upperCaseIdL <* symbolP SymDot)
  path <- upperCaseIdL `sepBy1` symbolP SymDot
  let (name, pos) = last path
  --  (name, pos) <- upperCaseIdL
  return (MkModuleName (fst <$> init path) name, pos)

classNameP :: Parser (ClassName, SourcePos)
classNameP = try $ do
  (name, pos) <- upperCaseIdL
  return (MkClassName name, pos)

primNameP :: Parser (PrimName, SourcePos)
primNameP = try $ do
  symbolP SymHash
  (name, pos) <- upperCaseIdL
  pure (MkPrimName name, pos)

methodNameP :: Parser (MethodName, SourcePos)
methodNameP = try $ do
  (name, pos) <- upperCaseIdL
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
    interOp = do
      symbolP SymInter <|> symbolP SymInterUnicode
      pos <- getSourcePos
      pure (InterOp, pos)
    unionOp = do
      symbolP SymUnion <|> symbolP SymUnionUnicode
      pos <- getSourcePos
      pure (UnionOp, pos)
    customOp = do
      (op, pos) <- tyOpNameP
      pure (CustomOp op, pos)
