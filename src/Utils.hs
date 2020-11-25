module Utils where

----------------------------------------------------------------------------------
-- Twice functor
----------------------------------------------------------------------------------

-- oftenly used data structure, so extracting it and making it a functor is useful
data Twice a = Twice a a deriving (Eq,Show)
twiceMap :: (a -> b) -> (a -> b) -> Twice a -> Twice b
twiceMap f g (Twice x y) = Twice (f x) (g y)

mergeTwice :: (a -> a -> a) -> Twice a -> a
mergeTwice f (Twice x y) = f x y

instance Functor Twice where
  fmap f = twiceMap f f


data Error
  = ParseError String
  | GenConstraintsError String
  | EvalError String
  | SolveConstraintsError String
  deriving (Show, Eq)
