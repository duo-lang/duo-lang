
module Syntax.NMap where

class NMap a b | a -> b where
  nmap  :: (b -> b) -> a -> a
  nmapM :: Monad m => (b -> m b) -> a -> m a

(<¢>) :: NMap a b => (b -> b) -> a -> a
(<¢>) = nmap

(<€>) :: (NMap a b, Monad m) => (b -> m b) -> a -> m a
(<€>) = nmapM

