module Parser.Types
  ( -- Kind Parser
    monoKindP
  , polyKindP
  , evalOrderP
  -- Type Parsers
  , typeSchemeP
  , typP
  , typAtomP
  , xtorDeclP
  , xtorSignatureP
  , returnP
  , combineXtors
  ) where

import Text.Megaparsec hiding (State)
import Data.List.NonEmpty (NonEmpty((:|)))

import Parser.Common
import Parser.Definition
import Parser.Lexer
import Syntax.CST.Types
import Syntax.Common.PrdCns
import Syntax.Common.Names
import Utils ( Loc(..) )
import Control.Monad (void)



---------------------------------------------------------------------------------
-- Parsing of linear contexts
---------------------------------------------------------------------------------
returnP :: Parser a -> Parser (PrdCns,a)
returnP p = do
  r <- optional (keywordP KwReturn)
  b <- p
  return $ case r of
    Just _ -> (Cns,b)
    Nothing -> (Prd,b)


xtorDeclP :: Parser (XtorName, [(PrdCns, Typ)])
xtorDeclP = do
  (xt, _pos) <- xtorNameP <?> "constructor/destructor name"
  args <- optional $ fst <$> (parens (returnP typP `sepBy` symbolP SymComma) <?> "argument list")
  return (xt, maybe [] (map (\(x,(y,_)) -> (x,y))) args)

-- | Parse a Constructor or destructor signature. E.g.
xtorSignatureP :: Parser XtorSig
xtorSignatureP = do
  (xt, pos) <- xtorDeclP
  return $ MkXtorSig xt (argListToLctxt pos)

argListToLctxt :: [(PrdCns, Typ)] -> LinearContext
argListToLctxt = fmap convert
  where
    convert (Prd, ty) = PrdType ty
    convert (Cns, ty) = CnsType ty

combineXtor :: (XtorName, [(PrdCns, Typ)]) -> XtorSig
combineXtor (xt, args) = MkXtorSig xt (argListToLctxt args)

combineXtors :: [(XtorName, [(PrdCns, Typ)])] -> [XtorSig]
combineXtors = fmap combineXtor

---------------------------------------------------------------------------------
-- Nominal and Structural Types
---------------------------------------------------------------------------------

nominalTypeArgsP :: SourcePos -> Parser ([Typ], SourcePos)
nominalTypeArgsP endPos = parens ((fst <$> typP) `sepBy` symbolP SymComma) <|> pure ([], endPos)

-- | Parse a nominal type.
-- E.g. "Nat", or "List(Nat)"
nominalTypeP :: Parser (Typ, SourcePos)
nominalTypeP = do
  startPos <- getSourcePos
  (name, endPos) <- typeNameP
  (args, endPos') <- nominalTypeArgsP endPos
  pure (TyNominal (Loc startPos endPos') name args, endPos')

-- | Parse a data or codata type. E.g.:
-- - "< ctor1 | ctor2 | ctor3 >"
-- - "{ dtor1 , dtor2 , dtor3 }"
xdataTypeP :: DataCodata -> Parser (Typ, SourcePos)
xdataTypeP Data = do
  startPos <- getSourcePos
  (xtorSigs, endPos) <- angles (xtorSignatureP `sepBy` symbolP SymComma)
  pure (TyXData (Loc startPos endPos) Data xtorSigs, endPos)
xdataTypeP Codata = do
  startPos <- getSourcePos
  (xtorSigs, endPos) <- braces (xtorSignatureP `sepBy` symbolP SymComma)
  pure (TyXData (Loc startPos endPos) Codata xtorSigs, endPos)



---------------------------------------------------------------------------------
-- Type variables and recursive types
---------------------------------------------------------------------------------

-- | Parses a typevariable, and checks whether the typevariable is bound.
typeVariableP :: Parser (Typ, SourcePos)
typeVariableP = do
  startPos <- getSourcePos
  (tvar, endPos) <- tvarP
  return (TySkolemVar (Loc startPos endPos) tvar, endPos)

recTypeP :: Parser (Typ, SourcePos)
recTypeP = do
  startPos <- getSourcePos
  _ <- keywordP KwRec
  (rv,_) <- tvarP
  _ <- symbolP SymDot
  (ty, endPos) <- typP
  pure (TyRec (Loc startPos endPos) rv ty, endPos)

---------------------------------------------------------------------------------
-- Refinement types
---------------------------------------------------------------------------------

refinementTypeP :: DataCodata -> Parser (Typ, SourcePos)
refinementTypeP Data = do
  startPos <- getSourcePos
  ((tn, ctors), endPos) <- angles (do
    (tn,_) <- typeNameP
    _ <- symbolP SymPipe
    ctors <- xtorSignatureP `sepBy` symbolP SymComma
    pure (tn, ctors))
  pure (TyXRefined (Loc startPos endPos) Data tn ctors, endPos)
refinementTypeP Codata = do
  startPos <- getSourcePos
  ((tn, dtors), endPos) <- braces (do
    (tn,_) <- typeNameP
    _ <- symbolP SymPipe
    dtors <- xtorSignatureP `sepBy` symbolP SymComma
    pure (tn, dtors))
  pure (TyXRefined (Loc startPos endPos) Codata tn dtors, endPos)

---------------------------------------------------------------------------------
-- Primitive types
---------------------------------------------------------------------------------

primTypeP :: Keyword -> (Loc -> Typ) -> Parser (Typ, SourcePos)
primTypeP kw constr = do
  startPos <- getSourcePos
  endPos <- keywordP kw
  pure (constr (Loc startPos endPos), endPos)

tyI64P :: Parser (Typ, SourcePos)
tyI64P = primTypeP KwI64 TyI64

tyF64P :: Parser (Typ, SourcePos)
tyF64P = primTypeP KwF64 TyF64

tyCharP :: Parser (Typ, SourcePos)
tyCharP = primTypeP KwChar TyChar

tyStringP :: Parser (Typ, SourcePos)
tyStringP = primTypeP KwString TyString

---------------------------------------------------------------------------------
-- Type Parser
---------------------------------------------------------------------------------

tyParensP :: Parser (Typ, SourcePos)
tyParensP = do
  startPos <- getSourcePos
  (typ, endPos) <- parens (fst <$> typP)
  pure (TyParens (Loc startPos endPos) typ, endPos)

tyTopP :: Parser (Typ, SourcePos)
tyTopP = do
  startPos <- getSourcePos
  endPos <- keywordP KwTop
  pure (TyTop (Loc startPos endPos), endPos)

tyBotP :: Parser (Typ, SourcePos)
tyBotP = do
  startPos <- getSourcePos
  endPos <- keywordP KwBot
  pure (TyBot (Loc startPos endPos), endPos)

-- | Parse atomic types (i,e, without tyop chains)
typAtomP :: Parser (Typ, SourcePos)
typAtomP = tyParensP
  <|> nominalTypeP
  <|> try (refinementTypeP Data)
  <|> try (refinementTypeP Codata)
  <|> xdataTypeP Data
  <|> xdataTypeP Codata
  <|> recTypeP
  <|> tyTopP
  <|> tyBotP
  <|> tyI64P
  <|> tyF64P
  <|> tyCharP
  <|> tyStringP
  <|> typeVariableP


tyOpChainP :: Parser (NonEmpty (Loc, BinOp, Typ), SourcePos)
tyOpChainP = do
  let f = do
          startPos <- getSourcePos
          (op, endPos) <- tyBinOpP
          (typ,pos) <- typAtomP
          pure ((Loc startPos endPos, op, typ), pos)
  lst <- some f
  case lst of
    [] -> error "Cannot occur, \"some\" parses non-empty list"
    (x:xs) -> pure (fst x :| (fst <$> xs), snd (last (x:xs)))

-- | Parse a type
typP :: Parser (Typ, SourcePos)
typP = do
  (fst, endPos) <- typAtomP
  maybeChain <- optional tyOpChainP
  case maybeChain of
    Nothing -> pure (fst, endPos)
    Just (chain, endPos) -> pure (TyBinOpChain fst chain, endPos)


---------------------------------------------------------------------------------
-- Parsing of type schemes.
---------------------------------------------------------------------------------

-- | Parse a type scheme
typeSchemeP :: Parser TypeScheme
typeSchemeP = do
  startPos <- getSourcePos
  tvars' <- option [] (keywordP KwForall >> some (fst <$> tvarP) <* symbolP SymDot)
  let constraintP = fst <$> (typeClassConstraintP <|> subTypeConstraintP)
  tConstraints <- option [] (constraintP `sepBy` symbolP SymComma <* symbolP SymDoubleRightArrow)
  (monotype, endPos) <- typP
  pure (TypeScheme (Loc startPos endPos) tvars' tConstraints monotype)

typeClassConstraintP :: Parser (Constraint, SourcePos)
typeClassConstraintP = try $ do
  cname <- fst <$> upperCaseId
  (tvar, pos) <- tvarP
  return (TypeClass (MkClassName cname) tvar, pos)

subTypeConstraintP :: Parser (Constraint, SourcePos)
subTypeConstraintP = try $ do
  t1 <- fst <$> typP
  void $ symbolP SymSubtype
  (t2, pos) <- typP
  return (SubType t1 t2, pos)
