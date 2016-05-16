module Eq_nat_dec where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect x f y =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec x f y =
  eq_rect x f y

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r x h y =
  eq_rec x h y

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

nat_rec :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rec =
  nat_rect

sumbool_rect :: (() -> a1) -> (() -> a1) -> Bool -> a1
sumbool_rect f f0 s =
  case s of {
   True -> f __;
   False -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Bool -> a1
sumbool_rec =
  sumbool_rect

eq_nat_dec :: Nat -> Nat -> Bool
eq_nat_dec n m =
  case n of {
   O ->
    case m of {
     O -> True;
     S n0 -> False};
   S n' ->
    case m of {
     O -> False;
     S m' -> eq_nat_dec n' m'}}

eq_nat_dec' :: Nat -> Nat -> Bool
eq_nat_dec' n m =
  nat_rec (\m0 ->
    case m0 of {
     O -> True;
     S n0 -> False}) (\n0 h m0 ->
    case m0 of {
     O -> False;
     S n1 -> sumbool_rec (\_ -> eq_rec_r n1 True n0) (\_ -> False) (h n1)}) n m

