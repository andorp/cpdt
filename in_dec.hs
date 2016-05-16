module In_dec where

import qualified Prelude

data List a =
   Nil
 | Cons a (List a)

in_dec :: (a1 -> a1 -> Bool) -> a1 -> (List a1) -> Bool
in_dec a_eq_dec x ls =
  case ls of {
   Nil -> False;
   Cons x' ls' ->
    case a_eq_dec x x' of {
     True -> True;
     False -> in_dec a_eq_dec x ls'}}

