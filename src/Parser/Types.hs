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

import Debug.Trace

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
-- Nominal and Structural Types
---------------------------------------------------------------------------------

-- | Parse a nominal type.
-- E.g. "Nat", or "List(Nat)"
nominalTypeP :: Parser (Typ, SourcePos)
nominalTypeP = do
  startPos <- getSourcePos
  (name, endPos) <- typeNameP
  sc
  pure (TyNominal (Loc startPos endPos) name, endPos)
 
-- | Parse a data or codata type. E.g.:
-- - "< ctor1 | ctor2 | ctor3 >"
-- - "{ dtor1 , dtor2 , dtor3 }"
xdataTypeP :: DataCodata -> Parser (Typ, SourcePos)
xdataTypeP Data = do
  startPos <- getSourcePos
  (xtorSigs, endPos) <- anglesP (xtorSignatureP `sepBy` (symbolP SymComma >> sc))
  sc
  pure (TyXData (Loc startPos endPos) Data xtorSigs, endPos)
xdataTypeP Codata = do
  startPos <- getSourcePos
  (xtorSigs, endPos) <- bracesP (xtorSignatureP `sepBy` (symbolP SymComma >> sc))
  sc
  pure (TyXData (Loc startPos endPos) Codata xtorSigs, endPos)



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
-- Refinement types
---------------------------------------------------------------------------------

refinementTypeP :: DataCodata -> Parser (Typ, SourcePos)
refinementTypeP Data = do
  startPos <- getSourcePos
  ((tn,rv,ctors), endPos) <- anglesP (do
    (tn,_) <- typeNameP
    sc
    symbolP SymPipe
    sc
    mrv <- optional tvarP
    case mrv of Nothing -> sc; Just _ -> sc >> symbolP SymPipe
    let rv = case mrv of Nothing -> Nothing; Just (rv',_) -> Just rv'
    sc
    ctors <- xtorSignatureP `sepBy` (symbolP SymComma >> sc)
    pure (tn, rv, ctors))
--  trace ("parsed refinement " <> show tn <> show endPos) $ pure ()
  pure (TyXRefined (Loc startPos endPos) Data tn rv ctors, endPos)
 
refinementTypeP Codata = do
  startPos <- getSourcePos
  ((tn, rv, dtors), endPos) <- bracesP (do
    (tn,_) <- typeNameP
    sc
    symbolP SymPipe
    sc
    mrv <- optional tvarP
    case mrv of Nothing -> sc; Just _ -> sc >> symbolP SymPipe
    let rv = case mrv of Nothing -> Nothing; Just (rv',_) -> Just rv'
    sc
    dtors <- xtorSignatureP `sepBy` (symbolP SymComma >> sc)
    pure (tn, rv, dtors))
--  trace ("parsed refinement " <> show tn) $ pure ()
  pure (TyXRefined (Loc startPos endPos) Codata tn rv dtors, endPos)

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
  args <- optional tyArgsP
--  trace ("parsed args " <> show args) $ pure ()
  endPos <- getSourcePos
--  trace ("endPos " <> show endPos) $ pure ()
  case args of
    Nothing -> pure (fstTy, endPos)
    Just (args',endPos) -> pure (TyApp (Loc startPos endPos) fstTy args',endPos)

tyArgsP :: Parser (NonEmpty Typ, SourcePos)
tyArgsP = do 
  symbolP SymAtSign
  sc
  symbolP SymParenLeft 
  sc
  args <- typP `sepBy1` (symbolP SymComma >> sc)
  sc
  symbolP SymParenRight
  sc
  endPos <- getSourcePos
  case args of 
    [] -> error ""
    ((ty1,_):argRst) -> pure (ty1:|map fst argRst,endPos)

tyOpChainP :: Parser (NonEmpty (Loc, BinOp, Typ), SourcePos)
tyOpChainP = do
  trace "parsing binopchain" $ pure ()
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
  trace "parsing atom " $  pure ()
  (fst, endPos) <- typAtomP
  trace ("parsed atom " <> show fst) $ pure ()
  maybeChain <- optional tyOpChainP
--  trace ("parsed chain " <> show maybeChain) $ pure ()
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
  let constraintP = fst <$> (typeClassConstraintP <|> subTypeConstraintP)
  tConstraints <- option [] (constraintP `sepBy` (symbolP SymComma >> sc) <* (symbolP SymDoubleRightArrow >> sc))
  (monotype, endPos) <- typP
  pure (TypeScheme (Loc startPos endPos) (fst <$> tvars') tConstraints monotype)

typeClassConstraintP :: Parser (Constraint, SourcePos)
typeClassConstraintP = try $ do
  (cname,_) <- classNameP
  sc
  (tvar, pos) <- tvarP
  sc
  return (TypeClass cname tvar, pos)

subTypeConstraintP :: Parser (Constraint, SourcePos)
subTypeConstraintP = try $ do
  t1 <- fst <$> typP
  symbolP SymSubtype
  sc
  (t2, pos) <- typP
  return (SubType t1 t2, pos)
