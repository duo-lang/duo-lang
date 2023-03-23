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
import Parser.Kinds
import Parser.Lexer
import Syntax.CST.Types
import Syntax.CST.Names
import Loc ( Loc(..) )
import Control.Monad (void)

---------------------------------------------------------------------------------
-- Parsing of linear contexts
---------------------------------------------------------------------------------
returnP :: Parser a -> Parser (PrdCns,a)
returnP p = do
  r <- optional (keywordP KwReturn >> sc)
  b <- p
  return $ case r of
    Just _ -> (Cns,b)
    Nothing -> (Prd,b)


xtorDeclP :: Parser (XtorName, [(PrdCns, Typ)])
xtorDeclP = do
  (xt, _pos) <- xtorNameP <?> "constructor/destructor name"
  args <- optional $ do
    (args,_) <- parensP (returnP typP `sepBy` (symbolP SymComma >> sc))
    pure args
  sc
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
-- Nominal Types
---------------------------------------------------------------------------------

-- | Parse a nominal type.
-- E.g. "Nat", or "List(Nat)"
nominalTypeP :: Parser (Typ, SourcePos)
nominalTypeP = do
  startPos <- getSourcePos
  (name, endPos) <- typeNameP
  sc
  let loc = Loc startPos endPos
  pure (TyNominal loc name, endPos)
 
---------------------------------------------------------------------------------
-- Structural Types and Refinement Types
---------------------------------------------------------------------------------

refinementArgsP :: Parser (Maybe (TypeName, Maybe SkolemTVar))
refinementArgsP = optional $ try $ do
  (tn,_) <- typeNameP
  sc
  symbolP SymPipe
  sc
  rv <- optional $ tvarP <* (sc >> symbolP SymPipe >> sc)
  pure (tn,fst <$> rv)


xdataOrRefinementP :: DataCodata -> Parser (Typ, SourcePos)
xdataOrRefinementP Data = do
  startPos <- getSourcePos
  symbolP SymAngleLeft
  sc
  refinementargs <- refinementArgsP
  ctors <- xtorSignatureP `sepBy` (symbolP SymComma >> sc)
  symbolP SymAngleRight
  endPos <- getSourcePos
  sc
  case refinementargs of
    Nothing -> pure (TyXData (Loc startPos endPos) Data ctors, endPos)
    Just (tn, Nothing) -> pure (TyXRefined (Loc startPos endPos) Data tn ctors, endPos)
    Just (tn, Just rv) -> pure (TyRec (Loc startPos endPos) rv (TyXRefined (Loc startPos endPos) Data tn ctors),endPos)

xdataOrRefinementP Codata = do
  startPos <- getSourcePos
  symbolP SymBraceLeft
  sc
  refinementargs <- refinementArgsP
  dtors <- xtorSignatureP `sepBy` (symbolP SymComma >> sc)
  symbolP SymBraceRight
  endPos <- getSourcePos
  sc
  case refinementargs of
    Nothing -> pure (TyXData (Loc startPos endPos) Codata dtors, endPos)
    Just (tn, Nothing) -> pure (TyXRefined (Loc startPos endPos) Codata tn dtors, endPos)
    Just (tn, Just rv) -> pure (TyRec (Loc startPos endPos) rv (TyXRefined (Loc startPos endPos) Codata tn dtors), endPos)


---------------------------------------------------------------------------------
-- Type variables and recursive types
---------------------------------------------------------------------------------

-- | Parses a typevariable, and checks whether the typevariable is bound.
typeVariableP :: Parser (Typ, SourcePos)
typeVariableP = do
  startPos <- getSourcePos
  (tvar, endPos) <- tvarP
  sc
  pure (TySkolemVar (Loc startPos endPos) tvar, endPos)

recTypeP :: Parser (Typ, SourcePos)
recTypeP = do
  startPos <- getSourcePos
  _ <- keywordP KwRec
  sc
  (rv,_) <- tvarP
  symbolP SymDot
  sc
  (ty, endPos) <- typP
  pure (TyRec (Loc startPos endPos) rv ty, endPos)


---------------------------------------------------------------------------------
-- Primitive types
---------------------------------------------------------------------------------

primTypeP :: Keyword -> (Loc -> Typ) -> Parser (Typ, SourcePos)
primTypeP kw constr = do
  startPos <- getSourcePos
  endPos <- keywordP kw
  sc
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
  sc
  symbolP SymParenLeft
  sc
  (typ, _) <- typP
  sc
  mmk <- optional (symbolP SymColon >> sc >> monoKindP)
  symbolP SymParenRight
  sc
  endPos <- getSourcePos
  case mmk of 
    Nothing -> pure (TyParens (Loc startPos endPos) typ, endPos)
    Just mk -> pure (TyKindAnnot mk typ, endPos)

tyTopKwP :: Parser SourcePos
tyTopKwP = kwASCII <|> kwUnicode
  where 
    kwASCII = keywordP KwTop
    kwUnicode = do
        symbolP SymTopUnicode
        getSourcePos

tyTopP :: Parser (Typ, SourcePos)
tyTopP = do
      startPos <- getSourcePos
      endPos <- tyTopKwP
      sc
      pure (TyTop (Loc startPos endPos), endPos)

tyBotKwP :: Parser SourcePos
tyBotKwP = kwASCII <|> kwUnicode
  where 
    kwASCII = keywordP KwBot
    kwUnicode = do
        symbolP SymBotUnicode
        getSourcePos

tyBotP :: Parser (Typ, SourcePos)
tyBotP = do
      startPos <- getSourcePos
      endPos <- tyBotKwP
      sc
      pure (TyBot (Loc startPos endPos), endPos)

-- | Parse atomic types (i,e, without tyop chains)
typAtomP :: Parser (Typ, SourcePos)
typAtomP = do 
  startPos <- getSourcePos
  (fstTy, _) <- 
    tyParensP
    <|> nominalTypeP
    <|> xdataOrRefinementP Data
    <|> xdataOrRefinementP Codata
    <|> recTypeP
    <|> tyTopP
    <|> tyBotP
    <|> tyI64P
    <|> tyF64P
    <|> tyCharP
    <|> tyStringP
    <|> typeVariableP
  args <- optional tyArgsP
  endPos <- getSourcePos
  case args of
    Nothing -> pure (fstTy, endPos)
    Just (args',endPos) -> pure (TyApp (Loc startPos endPos) fstTy (getTypeName fstTy) args',endPos)

tyArgsP :: Parser (NonEmpty Typ, SourcePos)
tyArgsP = do 
  symbolP SymParenLeft 
  sc
  args <- typP `sepBy1` (symbolP SymComma >> sc)
  symbolP SymParenRight
  endPos <- getSourcePos
  sc
  case args of 
    [] -> error "Unreachable: sepBy1 parses at least one element."
    ((ty1,_):argRst) -> pure (ty1:|map fst argRst,endPos)

tyOpChainP :: Parser (NonEmpty (Loc, BinOp, Typ), SourcePos)
tyOpChainP = do
  let f = do
          startPos <- getSourcePos
          (op, endPos) <- tyBinOpP
          sc
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

forallP :: Parser ()
forallP = void (keywordP KwForall) <|> symbolP SymForallUnicode

-- | Parse a type scheme
typeSchemeP :: Parser TypeScheme
typeSchemeP = do
  startPos <- getSourcePos
  tvars' <- option [] (forallP >> sc >> some (tvarAnnotP <* sc) <* (symbolP SymDot >> sc))
  (monotype, endPos) <- typP
  pure TypeScheme { loc = Loc startPos endPos
                  , vars = fst <$> tvars'
                  , monotype = monotype
  }
