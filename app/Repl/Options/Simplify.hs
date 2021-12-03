module Repl.Options.Simplify (simplifyOption) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Bifunctor (first)

import Errors ( Error(ParseError) )
import Parser.Parser ( runInteractiveParser, typeSchemeP )
import Pretty.Program ()
import Repl.Repl ( prettyRepl, Repl, Option(..) )
import Syntax.Types ( PolarityRep(..) )
import Text.Megaparsec (eof, errorBundlePretty)
import TypeAutomata.Simplify ( simplify )

simplifyCmd :: Text -> Repl ()
simplifyCmd s = case go PosRep of 
                    Right pp -> pp
                    Left err -> case go NegRep of
                      Right pp -> pp
                      Left err' -> do
                        prettyRepl ("Parsing type failed" :: String)
                        prettyRepl ("Positive parsing error:" :: String)
                        prettyRepl err
                        prettyRepl ("Negative parsing error:" :: String)
                        prettyRepl err'

  where
    go :: forall p. PolarityRep p -> Either Error (Repl ())
    go rep = do
      ty <- (first (ParseError . T.pack . errorBundlePretty) (runInteractiveParser (typeSchemeP rep <* eof) s))
      (_,tySimplified) <- simplify ty
      return $ prettyRepl tySimplified

simplifyOption :: Option
simplifyOption = Option
  { option_name = "simplify"
  , option_cmd = simplifyCmd
  , option_help = ["Simplify the given type."]
  , option_completer = Nothing
  }
