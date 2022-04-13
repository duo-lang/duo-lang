module Pretty.Pretty where

import Data.Text (Text)
import Data.Text qualified as T
import Prettyprinter
import Prettyprinter.Render.String (renderString)
import Prettyprinter.Render.Text (renderStrict)
import System.Console.ANSI

---------------------------------------------------------------------------------
-- Annotations
---------------------------------------------------------------------------------

data Annotation
  = AnnKeyword
  | AnnSymbol
  | AnnTypeName
  | AnnXtorName
  | AnnLiteral
  deriving (Show, Eq)

annKeyword :: Doc Annotation -> Doc Annotation
annKeyword = annotate AnnKeyword

annSymbol :: Doc Annotation -> Doc Annotation
annSymbol = annotate AnnSymbol

annTypeName :: Doc Annotation -> Doc Annotation
annTypeName = annotate AnnTypeName

annXtorName :: Doc Annotation -> Doc Annotation
annXtorName = annotate AnnXtorName

annLiteral :: Doc Annotation -> Doc Annotation
annLiteral = annotate AnnLiteral

-- A variant of the `Pretty` typeclass which uses our annotations.
-- Why the builtin  Pretty class is not sufficient, see: https://github.com/quchen/prettyprinter/issues/102
class PrettyAnn a where
  prettyAnn :: a -> Doc Annotation

instance {-# OVERLAPPING #-} PrettyAnn String where
  prettyAnn = pretty

instance PrettyAnn a => PrettyAnn [a] where
   prettyAnn xs = list (prettyAnn <$> xs)

instance PrettyAnn Text where
  prettyAnn = pretty

instance PrettyAnn Bool where
  prettyAnn = pretty

instance PrettyAnn () where
  prettyAnn = pretty

instance PrettyAnn Integer where
  prettyAnn = pretty

instance PrettyAnn Double where
  prettyAnn = pretty

---------------------------------------------------------------------------------
-- Render to String Backend
---------------------------------------------------------------------------------

ppPrint :: PrettyAnn a => a -> Text
ppPrint doc =
  let
    layout = defaultLayoutOptions { layoutPageWidth = AvailablePerLine 100 1 }
  in
    renderStrict (layoutPretty layout (prettyAnn doc))

ppPrintString :: PrettyAnn a => a -> String
ppPrintString doc =
  let
    layout = defaultLayoutOptions { layoutPageWidth = AvailablePerLine 100 1 }
  in
    renderString (layoutPretty layout (prettyAnn doc))


---------------------------------------------------------------------------------
-- Console Backend with ANSI Colors
---------------------------------------------------------------------------------

annotationToOpts :: Annotation -> [SGR]
annotationToOpts AnnKeyword  = [SetColor Foreground Vivid Blue]
annotationToOpts AnnSymbol   = [SetColor Foreground Dull Red]
annotationToOpts AnnTypeName = [SetColor Foreground Dull Green]
annotationToOpts AnnXtorName = [SetColor Foreground Dull Magenta]
annotationToOpts AnnLiteral  = [SetColor Foreground Dull Cyan]

ppPrintIO :: PrettyAnn a => a -> IO ()
ppPrintIO doc =
  let
    layout = defaultLayoutOptions { layoutPageWidth = AvailablePerLine 100 1 }
  in
    renderConsole (layoutPretty layout (prettyAnn doc))

renderConsole :: SimpleDocStream Annotation -> IO ()
renderConsole str = (renderConsole' str) >> putStrLn ""

renderConsole' :: SimpleDocStream Annotation -> IO ()
renderConsole' = \case
  SFail        -> return ()
  SEmpty       -> return ()
  SChar c x    -> do
    putStr $ c : []
    renderConsole' x
  SText _l t x -> do
    putStr (T.unpack t)
    renderConsole' x
  SLine i x    -> do
    putStr ('\n' : T.unpack (T.replicate i (T.singleton ' ')))
    renderConsole' x
  SAnnPush ann x -> do
    setSGR (annotationToOpts ann)
    renderConsole' x
  SAnnPop x    -> do
    setSGR [Reset]
    renderConsole' x

---------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------

intercalateX :: Doc ann -> [Doc ann] -> Doc ann
intercalateX  x xs = cat (punctuate x xs)

intercalateComma :: [Doc ann] -> Doc ann
intercalateComma xs = cat (punctuate comma xs)

-- | Layout of lists. Produces the following layout:
--
--   l x1
--   i x2
--   i x3
--   ...
--   i xn
--   r
mkParen :: Bool             -- ^ Whether to print the parens for empty list
        -> Doc Annotation   -- ^ Left paren symbol
        -> Doc Annotation   -- ^ Right paren symbol
        -> Doc Annotation   -- ^ Interspersed character
        -> [Doc Annotation] -- ^ Elements
        -> Doc Annotation
mkParen True  l r _ []     = l <> r
mkParen False _ _ _ []     = mempty
mkParen _ l r _ [x]    = l <+> x <+> r
mkParen _ l r i (x:xs) = align $ sep list
  where
    list = ((l <+> x) : [ i <+> x' | x' <- xs]) ++ [r]

parens' :: Doc Annotation -> [Doc Annotation] -> Doc Annotation
parens' = mkParen False (prettyAnn ("(" :: String))(prettyAnn (")" :: String))

--brackets' :: Doc Annotation -> [Doc Annotation] -> Doc Annotation
--brackets' = mkParen False (prettyAnn ("[" :: String))(prettyAnn ("]" :: String))

angles' :: Doc Annotation -> [Doc Annotation] -> Doc Annotation
angles' = mkParen True (prettyAnn ("<" :: String))(prettyAnn (">" :: String))

braces' :: Doc Annotation -> [Doc Annotation] -> Doc Annotation
braces' = mkParen True (prettyAnn ("{" :: String))(prettyAnn ("}" :: String))
