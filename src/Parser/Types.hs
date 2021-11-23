module Parser.Types
  ( -- Kind Parser
    kindP
    -- Type Parsers
  , typeSchemeP
  , typP
    -- Invariant Types
  , Invariant(..)
  , invariantP
  ) where

import Control.Monad.State
import Control.Monad.Reader
import Data.Set qualified as S
import Text.Megaparsec hiding (State)

import Parser.Definition
import Parser.Lexer
import Syntax.CommonTerm
import Syntax.Types
import Syntax.Kinds

---------------------------------------------------------------------------------
-- Parsing of Kinds
---------------------------------------------------------------------------------

-- | Parses one of the keywords "CBV" or "CBN"
callingConventionP :: Parser CallingConvention
callingConventionP = cbvKwP *> return CBV <|> cbnKwP *> return CBN

-- | Parses a MonoKind, either "Type CBV" or "Type CBN"
kindP :: Parser Kind
kindP = do
  _ <- typeKwP
  cc <- callingConventionP
  return $ MonoKind cc

---------------------------------------------------------------------------------
-- Parsing of linear contexts
---------------------------------------------------------------------------------

-- | Parse a parenthesized list of producer types.
-- E.g.: "(Nat, Bool, { 'Ap(Nat)[Bool] })"
prdCtxtPartP :: PolarityRep pol -> Parser (LinearContext pol)
prdCtxtPartP rep = do
  (res,_) <- parens $ (PrdType <$> typP rep) `sepBy` comma
  return res

-- | Parse a bracketed list of consumer types.
-- E.g.: "[Nat, Bool, { 'Ap(Nat)[Bool] }]"
cnsCtxtPartP :: PolarityRep pol -> Parser (LinearContext pol)
cnsCtxtPartP rep = do
  (res,_) <- brackets $ (CnsType <$> typP (flipPolarityRep rep)) `sepBy` comma
  return res

-- | Parse a linear context.
-- E.g.: "(Nat,Bool)[Int](Int)[Bool,Float]"
linearContextP :: PolarityRep pol -> Parser (LinearContext pol)
linearContextP rep = concat <$> (many (prdCtxtPartP rep <|> cnsCtxtPartP rep))


---------------------------------------------------------------------------------
-- Nominal and Structural Types
---------------------------------------------------------------------------------

-- | Parse a nominal type.
-- E.g. "Nat"
nominalTypeP :: PolarityRep pol -> Parser (Typ pol)
nominalTypeP rep = do
  (name, _pos) <- typeNameP
  pure $ TyNominal rep Nothing name


-- | Parse a data or codata type. E.g.:
-- - "< ctor1 | ctor2 | ctor3 >"
-- - "{ dtor1 , dtor2 , dtor3 }"
xdataTypeP :: DataCodataRep dc -> PolarityRep pol -> Parser (Typ pol)
xdataTypeP DataRep polrep = fst <$> angles (do
  xtorSigs <- xtorSignatureP polrep `sepBy` pipe
  return (TyData polrep Nothing xtorSigs))
xdataTypeP CodataRep polrep = fst <$> braces (do
  xtorSigs <- xtorSignatureP (flipPolarityRep polrep) `sepBy` comma
  return (TyCodata polrep Nothing xtorSigs))

-- | Parse a Constructor or destructor signature. E.g.
-- - "Cons(Nat,List)"
-- - "'Head[Nat]"
xtorSignatureP :: PolarityRep pol -> Parser (XtorSig pol)
xtorSignatureP rep = do
  (xt, _pos) <- xtorName Structural <|> xtorName Nominal
  lctxt <- linearContextP rep
  return (MkXtorSig xt lctxt)

---------------------------------------------------------------------------------
-- Type variables and recursive types
---------------------------------------------------------------------------------

-- | Parses a typevariable, and checks whether the typevariable is bound.
typeVariableP :: PolarityRep pol -> Parser (Typ pol)
typeVariableP rep = do
  tvs <- asks tvars
  tv <- MkTVar . fst <$> freeVarName
  guard (tv `S.member` tvs)
  return $ TyVar rep Nothing tv

recTypeP :: PolarityRep pol -> Parser (Typ pol)
recTypeP rep = do
  _ <- recKwP
  rv <- MkTVar . fst <$> freeVarName
  _ <- dot
  ty <- local (\tpr@ParseReader{ tvars } -> tpr { tvars = S.insert rv tvars }) (typP rep)
  return $ TyRec rep rv ty

---------------------------------------------------------------------------------
-- Refinement types
---------------------------------------------------------------------------------

refinementTypeP :: PolarityRep pol -> Parser (Typ pol)
refinementTypeP rep = fst <$> dbraces (do
  (tn,_) <- typeNameP
  _ <- refineSym
  ty <- typP rep
  case ty of
    TyData _ Nothing ctors -> return $ TyData rep (Just tn) ctors
    TyCodata _ Nothing dtors -> return $ TyCodata rep (Just tn) dtors
    _ -> error "Second component of refinement type must be data or codata type"
  )

---------------------------------------------------------------------------------
-- Lattice types
---------------------------------------------------------------------------------

sepBy2 :: Parser a -> Parser sep -> Parser [a]
sepBy2 p sep = do
  fst <- p
  _ <- sep
  rest <- sepBy1 p sep
  return (fst : rest)

-- | Parse "Top" or "Bot".
topBotP :: PolarityRep pol -> Parser (Typ pol)
topBotP PosRep = botKwP *> return (TySet PosRep Nothing [])
topBotP NegRep = topKwP *> return (TySet NegRep Nothing [])

-- | Parse a union or intersection of types. I.e.
-- - "ty1 /\ ty2 /\ ty3"
-- - "ty1 \/ ty2 \/ ty3"
unionInterP :: PolarityRep pol -> Parser (Typ pol)
unionInterP PosRep = TySet PosRep Nothing <$> (typP' PosRep) `sepBy2` unionSym
unionInterP NegRep = TySet NegRep Nothing <$> (typP' NegRep) `sepBy2` intersectionSym

setTypeP :: PolarityRep pol -> Parser (Typ pol)
setTypeP rep = topBotP rep <|> unionInterP rep

---------------------------------------------------------------------------------
-- Type Parser
---------------------------------------------------------------------------------

-- Without joins and meets
typP' :: PolarityRep pol -> Parser (Typ pol)
typP' rep = try (fst <$> parens (typP rep)) <|>
  nominalTypeP rep <|>
  refinementTypeP rep <|>
  xdataTypeP DataRep rep <|>
  xdataTypeP CodataRep rep <|>
  recTypeP rep <|>
  typeVariableP rep

typP :: PolarityRep pol -> Parser (Typ pol)
typP rep = try (setTypeP rep) <|> typP' rep

---------------------------------------------------------------------------------
-- Parsing of invariant Types (HACKY!)
---------------------------------------------------------------------------------

newtype Invariant = MkInvariant { unInvariant :: forall pol. PolarityRep pol -> Typ pol }

-- DO NOT EXPORT! Hacky workaround.
switchPol :: Typ pol -> Typ (FlipPol pol)
switchPol (TyVar rep kind tv) = TyVar (flipPolarityRep rep) kind tv
switchPol (TyData rep mtn xtors) = TyData (flipPolarityRep rep) mtn (switchSig <$> xtors)
switchPol (TyCodata rep mtn xtors) = TyCodata (flipPolarityRep rep) mtn (switchSig <$> xtors)
switchPol (TyNominal rep kind tn) = TyNominal (flipPolarityRep rep) kind tn
switchPol (TySet rep kind typs) = TySet (flipPolarityRep rep) kind (switchPol <$> typs)
switchPol (TyRec rep tv typ) = TyRec (flipPolarityRep rep) tv (switchPol typ)

switchSig :: XtorSig pol -> XtorSig (FlipPol pol)
switchSig (MkXtorSig xt ctxt) = MkXtorSig xt (switchCtxt ctxt)

switchCtxt :: LinearContext pol -> LinearContext (FlipPol pol)
switchCtxt = undefined

invariantP :: Parser Invariant
invariantP = do
  typ <- typP' PosRep
  pure $ MkInvariant $ \rep -> case rep of PosRep -> typ ; NegRep -> switchPol typ


---------------------------------------------------------------------------------
-- Parsing of type schemes.
---------------------------------------------------------------------------------

typeSchemeP :: PolarityRep pol -> Parser (TypeScheme pol)
typeSchemeP polrep = do
  tvars' <- S.fromList <$> option [] (forallKwP >> some (MkTVar . fst <$> freeVarName) <* dot)
  monotype <- local (\s -> s { tvars = tvars' }) (typP polrep)
  if S.fromList (freeTypeVars monotype) `S.isSubsetOf` tvars'
    then return (TypeScheme (S.toList tvars') monotype)
    else fail "Forall annotation in type scheme is incorrect"

