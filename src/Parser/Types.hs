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
import Control.Monad.Reader ( asks, MonadReader(local) )
import Data.Set qualified as S
import Text.Megaparsec hiding (State)

import Parser.Definition
import Parser.Lexer
import Syntax.CommonTerm
import Syntax.Kinds
import qualified Syntax.Types as AST
import Syntax.Types (DataCodata (Data, Codata), PolarityRep, TVar (MkTVar))
import Syntax.CST.Types
import Data.Text
import Syntax.CST.Lowering (lowerTyp, lowerTypeScheme)

---------------------------------------------------------------------------------
-- Parsing of Kinds
---------------------------------------------------------------------------------

-- | Parses one of the keywords "CBV" or "CBN"
callingConventionP :: Parser CallingConvention
callingConventionP = CBV <$ cbvKwP <|> CBN <$ cbnKwP

-- | Parses a MonoKind, either "Type CBV" or "Type CBN"
kindP :: Parser Kind
kindP = do
  _ <- typeKwP
  MonoKind <$> callingConventionP

---------------------------------------------------------------------------------
-- Parsing of linear contexts
---------------------------------------------------------------------------------

-- | Parse a parenthesized list of producer types.
-- E.g.: "(Nat, Bool, { 'Ap(Nat)[Bool] })"
prdCtxtPartP :: Parser LinearContext
prdCtxtPartP = do
  (res, _) <- parens $ (PrdType <$> typP') `sepBy` comma
  return res

-- | Parse a bracketed list of consumer types.
-- E.g.: "[Nat, Bool, { 'Ap(Nat)[Bool] }]"
cnsCtxtPartP :: Parser LinearContext
cnsCtxtPartP = do
  (res,_) <- brackets $ (CnsType <$> typP' ) `sepBy` comma
  return res

-- | Parse a linear context.
-- E.g.: "(Nat,Bool)[Int](Int)[Bool,Float]"
linearContextP :: Parser LinearContext
linearContextP = Prelude.concat <$> many (prdCtxtPartP <|> cnsCtxtPartP)

---------------------------------------------------------------------------------
-- Nominal and Structural Types
---------------------------------------------------------------------------------

-- | Parse a nominal type.
-- E.g. "Nat"
nominalTypeP :: Parser Typ
nominalTypeP = do
  (name, _pos) <- typeNameP
  pure $ TyNominal name

-- | Parse a data or codata type. E.g.:
-- - "< ctor1 | ctor2 | ctor3 >"
-- - "{ dtor1 , dtor2 , dtor3 }"
xdataTypeP :: DataCodata -> Parser Typ
xdataTypeP Data = fst <$> angles (do
  xtorSigs <- xtorSignatureP `sepBy` pipe
  return (TyXData Data Nothing xtorSigs))
xdataTypeP Codata = fst <$> braces (do
  xtorSigs <- xtorSignatureP `sepBy` comma
  return (TyXData Codata Nothing xtorSigs))

-- | Parse a Constructor or destructor signature. E.g.
-- - "Cons(Nat,List)"
-- - "'Head[Nat]"
xtorSignatureP :: Parser XtorSig
xtorSignatureP = do
  (xt, _pos) <- xtorName Structural <|> xtorName Nominal
  MkXtorSig xt <$> linearContextP

---------------------------------------------------------------------------------
-- Type variables and recursive types
---------------------------------------------------------------------------------

-- | Parses a typevariable, and checks whether the typevariable is bound.
typeVariableP :: Parser Typ
typeVariableP = do
  tvs <- asks tvars
  tv <- MkTVar . fst <$> freeVarName
  guard (tv `S.member` tvs)
  return $ TyVar tv

recTypeP :: Parser Typ
recTypeP = do
  _ <- recKwP
  rv <- MkTVar . fst <$> freeVarName
  _ <- dot
  ty <- local (\tpr@ParseReader{ tvars } -> tpr { tvars = S.insert rv tvars }) typP'
  return $ TyRec rv ty

---------------------------------------------------------------------------------
-- Refinement types
---------------------------------------------------------------------------------

refinementTypeP :: Parser Typ
refinementTypeP = fst <$> dbraces (do
  (tn,_) <- typeNameP
  _ <- refineSym
  ty <- typP'
  case ty of
    TyXData dc Nothing ctors -> return $ TyXData dc (Just tn) ctors
    _ -> error "Second component of refinement type must be data or codata type"
  )

---------------------------------------------------------------------------------
-- Type Parser
---------------------------------------------------------------------------------

-- | Parse atomic types
typAtomP :: Parser Typ
typAtomP = (TyParens . fst <$> parens typP')
  <|> nominalTypeP
  <|> refinementTypeP
  <|> xdataTypeP Data
  <|> xdataTypeP Codata
  <|> recTypeP
  <|> TyTop <$ topKwP
  <|> TyBot <$ botKwP
  <|> typeVariableP

tyOpP :: Parser Text
tyOpP = "->" <$ thinRightarrow
    <|> "/\\" <$ intersectionSym
    <|> "\\/" <$ unionSym

opsChainP' :: Parser a -> Parser b -> Parser [(b, a)]
opsChainP' p op = do
  let fst = try ((,) <$> op <*> p)
  let rest = opsChainP' p op
  ((:) <$> fst <*> rest) <|> pure []

opsChainP :: Parser a -> Parser b -> Parser (a, [(b, a)])
opsChainP p op = do
  (fst, (o, snd)) <- try (((,) <$> p) <*> (((,) <$> op) <*> p))
  rest <- opsChainP' p op
  pure (fst, (o, snd) : rest)

-- | Parse a chain of type operators
typOpsP :: Parser Typ
typOpsP = uncurry TyBinOpChain <$> opsChainP typAtomP tyOpP

-- | Parse a type
typP' :: Parser Typ
typP' = typOpsP <|> typAtomP

-- | Parse a type and lower it
typP :: PolarityRep pol -> Parser (AST.Typ pol)
typP rep = do
  t <- typP'
  case lowerTyp rep t of
    Right t -> pure t
    Left err -> fail (show err)

---------------------------------------------------------------------------------
-- Parsing of invariant Types (HACKY!)
---------------------------------------------------------------------------------

newtype Invariant = MkInvariant { unInvariant :: forall pol. PolarityRep pol -> AST.Typ pol }

invariantP :: Parser Invariant
invariantP = do
  typ <- typAtomP
  pure $ MkInvariant $ \rep ->
    case lowerTyp rep typ of
      Right typ -> typ
      -- FIXME: Adjust AST such that it can handle lazy lowering/polarization properly
      Left err -> error (show err)

---------------------------------------------------------------------------------
-- Parsing of type schemes.
---------------------------------------------------------------------------------

-- | Parse a type scheme
typeSchemeP' :: Parser TypeScheme
typeSchemeP' = do
  tvars' <- S.fromList <$> option [] (forallKwP >> some (MkTVar . fst <$> freeVarName) <* dot)
  monotype <- local (\s -> s { tvars = tvars' }) typP'
  pure (TypeScheme tvars' monotype)

-- | Parse a type scheme and lower it
typeSchemeP :: PolarityRep pol -> Parser (AST.TypeScheme pol)
typeSchemeP rep = do
  s <- typeSchemeP'
  case lowerTypeScheme rep s of
    Right s -> pure s
    Left err -> fail (show err)
