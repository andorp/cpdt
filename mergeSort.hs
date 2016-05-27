module MergeSort where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

data Bool =
   True
 | False

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

data Prod a b =
   Pair a b

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x y -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair x y -> y}

data List a =
   Nil
 | Cons a (List a)

length :: (List a1) -> Nat
length l =
  case l of {
   Nil -> O;
   Cons y l' -> S (length l')}

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

fix_F :: (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
fix_F f x =
  f x (\y _ -> fix_F f y)

fix :: (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
fix f x =
  fix_F f x

le_lt_dec :: Nat -> Nat -> Sumbool
le_lt_dec n m =
  nat_rec (\m0 -> Left) (\n0 iHn m0 ->
    case m0 of {
     O -> Right;
     S m1 -> sumbool_rec (\_ -> Left) (\_ -> Right) (iHn m1)}) n m

insert :: (a1 -> a1 -> Bool) -> a1 -> (List a1) -> List a1
insert le x ls =
  case ls of {
   Nil -> Cons x Nil;
   Cons h ls' ->
    case le x h of {
     True -> Cons x ls;
     False -> Cons h (insert le x ls')}}

merge :: (a1 -> a1 -> Bool) -> (List a1) -> (List a1) -> List a1
merge le ls1 ls2 =
  case ls1 of {
   Nil -> ls2;
   Cons h ls' -> insert le h (merge le ls' ls2)}

split :: (List a1) -> Prod (List a1) (List a1)
split ls =
  case ls of {
   Nil -> Pair Nil Nil;
   Cons h1 l ->
    case l of {
     Nil -> Pair (Cons h1 Nil) Nil;
     Cons h2 ls' ->
      case split ls' of {
       Pair ls1 ls2 -> Pair (Cons h1 ls1) (Cons h2 ls2)}}}

mergeSort :: (a1 -> a1 -> Bool) -> (List a1) -> List a1
mergeSort le =
  fix (\ls mergeSort0 ->
    case le_lt_dec (S (S O)) (length ls) of {
     Left ->
      let {lss = split ls} in merge le (mergeSort0 (fst lss) __) (mergeSort0 (snd lss) __);
     Right -> ls})

