module Pred where

import qualified Prelude

data Nat =
   O
 | S Nat

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
pred :: Nat -> Nat
pred n =
  case n of {
   O -> n;
   S u -> u}

pred_strong1 :: Nat -> Nat
pred_strong1 n =
  case n of {
   O -> Prelude.error "absurd case";
   S n' -> n'}

pred_strong2 :: Nat -> Nat
pred_strong2 s =
  case s of {
   O -> Prelude.error "absurd case";
   S n' -> n'}

pred_strong3 :: Nat -> Nat
pred_strong3 s =
  case s of {
   O -> Prelude.error "absurd case";
   S n' -> n'}

