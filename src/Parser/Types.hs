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

import Parser.Common
import Parser.Definition
import Parser.Lexer
import Syntax.Common
import Syntax.CST.Types
import Utils ( Loc(..) )



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
-- E.g. "Nat", or "List(Nat)"
nominalTypeP :: Parser Typ
nominalTypeP = do
  startPos <- getSourcePos 
  (name, endPos) <- typeNameP
  args <- nominalTypeArgsP
  pure $ TyNominal (Loc startPos endPos) name args

-- | Parse a data or codata type. E.g.:
-- - "< ctor1 | ctor2 | ctor3 >"
-- - "{ dtor1 , dtor2 , dtor3 }"
xdataTypeP :: DataCodata -> Parser Typ
xdataTypeP Data = do
  startPos <- getSourcePos
  (xtorSigs, endPos) <- angles (xtorSignatureP `sepBy` symbolP SymComma)
  pure (TyXData (Loc startPos endPos) Data Nothing xtorSigs)
xdataTypeP Codata = do
  startPos <- getSourcePos 
  (xtorSigs, endPos) <- braces (xtorSignatureP `sepBy` symbolP SymComma)
  pure (TyXData (Loc startPos endPos) Codata Nothing xtorSigs)

-- | Parse a Constructor or destructor signature. E.g.
-- - "Cons(Nat,List)"
-- - "Head[Nat]"
xtorSignatureP :: Parser XtorSig
xtorSignatureP = do
  (xt, _pos) <- xtorNameP
  MkXtorSig xt <$> linearContextP

---------------------------------------------------------------------------------
-- Type variables and recursive types
---------------------------------------------------------------------------------

-- | Parses a typevariable, and checks whether the typevariable is bound.
typeVariableP :: Parser Typ
typeVariableP = do
  startPos <- getSourcePos
  tvs <- asks tvars
  (tvar, endPos) <- tvarP
  guard (tvar `S.member` tvs)
  return $ TyVar (Loc startPos endPos) tvar

recTypeP :: Parser Typ
recTypeP = do
  startPos <- getSourcePos
  _ <- keywordP KwRec
  (rv,_) <- tvarP
  _ <- symbolP SymDot
  ty <- local (\tpr@ParseReader{ tvars } -> tpr { tvars = S.insert rv tvars }) typP
  pure $ TyRec (Loc startPos startPos) rv ty -- TODO

---------------------------------------------------------------------------------
-- Refinement types
---------------------------------------------------------------------------------

refinementTypeP :: DataCodata -> Parser Typ
refinementTypeP Data = do
  startPos <- getSourcePos
  ((tn, ctors), endPos) <- angles (do
    (tn,_) <- typeNameP
    _ <- symbolP SymPipe
    ctors <- xtorSignatureP `sepBy` symbolP SymComma
    pure (tn, ctors))
  pure $ TyXData (Loc startPos endPos) Data (Just tn) ctors
refinementTypeP Codata = do
  startPos <- getSourcePos
  ((tn, dtors), endPos) <- braces (do
    (tn,_) <- typeNameP
    _ <- symbolP SymPipe
    dtors <- xtorSignatureP `sepBy` symbolP SymComma
    pure (tn, dtors))
  pure $ TyXData (Loc startPos endPos) Codata (Just tn) dtors

---------------------------------------------------------------------------------
-- Primitive types
---------------------------------------------------------------------------------

primitiveTypeP :: Parser (PrimitiveType, SourcePos)
primitiveTypeP =
  (keywordP KwI64 >>= \pos -> pure (I64, pos)) <|>
  (keywordP KwF64 >>= \pos -> pure (F64, pos))

tyPrimP :: Parser Typ
tyPrimP = do
  startPos <- getSourcePos
  (primitiveType, endPos) <- primitiveTypeP
  pure $ TyPrim (Loc startPos endPos) primitiveType

---------------------------------------------------------------------------------
-- Type Parser
---------------------------------------------------------------------------------

tyParensP :: Parser Typ
tyParensP = do
  startPos <- getSourcePos
  (typ, endPos) <- parens typP
  pure $ TyParens (Loc startPos endPos) typ

tyTopP :: Parser Typ
tyTopP = do
  startPos <- getSourcePos
  endPos <- keywordP KwTop
  pure $ TyTop (Loc startPos endPos)

tyBotP :: Parser Typ
tyBotP = do
  startPos <- getSourcePos
  endPos <- keywordP KwBot
  pure $ TyBot (Loc startPos endPos)

-- | Parse atomic types (i,e, without tyop chains)
typAtomP :: Parser Typ
typAtomP = tyParensP
  <|> nominalTypeP
  <|> try (refinementTypeP Data)
  <|> try (refinementTypeP Codata)
  <|> xdataTypeP Data
  <|> xdataTypeP Codata
  <|> recTypeP
  <|> tyTopP
  <|> tyBotP
  <|> tyPrimP
  <|> typeVariableP


tyOpChainP :: Parser (NonEmpty (Loc, BinOp, Typ))
tyOpChainP = do
  let f = do
          startPos <- getSourcePos
          (op, endPos) <- tyBinOpP
          typ <- typAtomP
          pure ((Loc startPos endPos), op, typ)
  lst <- some f
  case lst of
    [] -> error "Cannot occur, \"some\" parses non-empty list"
    (x:xs) -> pure (x :| xs)

-- | Parse a type
typP :: Parser Typ
typP = do
  fst <- typAtomP
  maybeChain <- optional tyOpChainP
  case maybeChain of
    Nothing -> pure fst
    Just chain -> pure (TyBinOpChain fst chain)


---------------------------------------------------------------------------------
-- Parsing of type schemes.
---------------------------------------------------------------------------------

-- | Parse a type scheme
typeSchemeP :: Parser TypeScheme
typeSchemeP = do
  tvars' <- option [] (keywordP KwForall >> some (fst <$> tvarP) <* symbolP SymDot)
  monotype <- local (\s -> s { tvars = S.fromList tvars' }) typP
  pure (TypeScheme tvars' monotype)
