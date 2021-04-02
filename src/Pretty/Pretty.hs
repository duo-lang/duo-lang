{-# LANGUAGE OverloadedStrings #-}
module Pretty.Pretty where

import qualified Data.Text as T
import Prettyprinter
import Prettyprinter.Render.String (renderString)
import System.Console.ANSI

import Syntax.CommonTerm

import Utils

---------------------------------------------------------------------------------
-- Annotations
---------------------------------------------------------------------------------

data Annotation
  = AnnKeyword
  | AnnSymbol
  | AnnTypeName
  | AnnXtorName
  deriving (Show, Eq)

annKeyword :: Doc Annotation -> Doc Annotation
annKeyword = annotate AnnKeyword

annSymbol :: Doc Annotation -> Doc Annotation
annSymbol = annotate AnnSymbol

annTypeName :: Doc Annotation -> Doc Annotation
annTypeName = annotate AnnTypeName

annXtorName :: Doc Annotation -> Doc Annotation
annXtorName = annotate AnnXtorName

-- A variant of the `Pretty` typeclass which uses our annotations.
-- Why the builtin  Pretty class is not sufficient, see: https://github.com/quchen/prettyprinter/issues/102
class PrettyAnn a where
  prettyAnn :: a -> Doc Annotation

instance {-# OVERLAPPING #-} PrettyAnn String where
  prettyAnn = pretty

instance PrettyAnn a => PrettyAnn [a] where
  prettyAnn xs = list (prettyAnn <$> xs)

instance PrettyAnn Bool where
  prettyAnn = pretty

instance PrettyAnn () where
  prettyAnn = pretty

---------------------------------------------------------------------------------
-- Render to String Backend
---------------------------------------------------------------------------------

ppPrint :: PrettyAnn a => a -> String
ppPrint doc =
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

prettyTwice' :: (PrettyAnn a, PrettyAnn b) => [a] -> [b] -> Doc Annotation
prettyTwice' xs ys = xs' <> ys'
  where
    xs' = if null xs then mempty else parens   (intercalateComma (map prettyAnn xs))
    ys' = if null ys then mempty else brackets (intercalateComma (map prettyAnn ys))

prettyTwice :: PrettyAnn a => Twice [a] -> Doc Annotation
prettyTwice (Twice xs ys) = prettyTwice' xs ys

instance PrettyAnn XtorName where
  prettyAnn (MkXtorName Structural xt) = annXtorName $ "'" <> prettyAnn xt
  prettyAnn (MkXtorName Nominal    xt) = annXtorName $ prettyAnn xt

-- | This identity wrapper is used to indicate that we want to transform the element to
-- a named representation before prettyprinting it.
newtype NamedRep a = NamedRep a

