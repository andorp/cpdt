module Type_check where

import qualified Prelude

data Bool =
   True
 | False

data Nat =
   O
 | S Nat

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
data Sumor a =
   Inleft a
 | Inright

data Maybe a =
   Unknown
 | Found a

data Exp =
   Nat0 Nat
 | Plus Exp Exp
 | Bool0 Bool
 | And Exp Exp

data Type =
   TNat
 | TBool

type_rect :: a1 -> a1 -> Type -> a1
type_rect f f0 t =
  case t of {
   TNat -> f;
   TBool -> f0}

type_rec :: a1 -> a1 -> Type -> a1
type_rec =
  type_rect

eq_type_dec :: Type -> Type -> Bool
eq_type_dec t1 t2 =
  type_rec (\t0 ->
    case t0 of {
     TNat -> True;
     TBool -> False}) (\t0 ->
    case t0 of {
     TNat -> False;
     TBool -> True}) t1 t2

typeCheck :: Exp -> Maybe Type
typeCheck e =
  case e of {
   Nat0 n -> Found TNat;
   Plus e1 e2 ->
    case typeCheck e1 of {
     Unknown -> Unknown;
     Found t1 ->
      case typeCheck e2 of {
       Unknown -> Unknown;
       Found t2 ->
        case eq_type_dec t1 TNat of {
         True ->
          case eq_type_dec t2 TNat of {
           True -> Found TNat;
           False -> Unknown};
         False -> Unknown}}};
   Bool0 b -> Found TBool;
   And e1 e2 ->
    case typeCheck e1 of {
     Unknown -> Unknown;
     Found t1 ->
      case typeCheck e2 of {
       Unknown -> Unknown;
       Found t2 ->
        case eq_type_dec t1 TBool of {
         True ->
          case eq_type_dec t2 TBool of {
           True -> Found TBool;
           False -> Unknown};
         False -> Unknown}}}}

typeCheck' :: Exp -> Sumor Type
typeCheck' e =
  case e of {
   Nat0 n -> Inleft TNat;
   Plus e1 e2 ->
    case typeCheck' e1 of {
     Inleft s ->
      case typeCheck' e2 of {
       Inleft s0 ->
        case eq_type_dec s TNat of {
         True ->
          case eq_type_dec s0 TNat of {
           True -> Inleft TNat;
           False -> Inright};
         False -> Inright};
       Inright -> Inright};
     Inright -> Inright};
   Bool0 b -> Inleft TBool;
   And e1 e2 ->
    case typeCheck' e1 of {
     Inleft s ->
      case typeCheck' e2 of {
       Inleft s0 ->
        case eq_type_dec s TBool of {
         True ->
          case eq_type_dec s0 TBool of {
           True -> Inleft TBool;
           False -> Inright};
         False -> Inright};
       Inright -> Inright};
     Inright -> Inright}}

