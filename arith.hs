module Arith where

import qualified Prelude

data Nat =
   O
 | S Nat

plus :: Nat -> Nat -> Nat
plus n m =
  case n of {
   O -> m;
   S n' -> S (plus n' m)}

