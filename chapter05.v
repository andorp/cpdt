
(* 5 Infinite Data and Proofs *)

Require Import List.
Set Implicit Arguments.


(* 5.1 Computing with Infinite Data *)

Section stream.
  Variable A : Type.
  CoInductive stream : Type :=
  | Cons : A -> stream -> stream
  .
End stream.

(*
Rather, whereas recursive definitions were necessary to use values of recursive
inductive types effectively, here we find that we need co-recursive definitions
to build values of co-inductive types effectively.
*)

CoFixpoint zeroes : stream nat := Cons 0 zeroes.

CoFixpoint trues_falses : stream bool := Cons true falses_trues
with falses_trues : stream bool := Cons false trues_falses
.

Fixpoint approx A (s : stream A) (n : nat) : list A :=
  match n with
  | O => nil
  | S n' =>
    match s with
    | Cons h t => h :: approx t n'
    end
  end
.

Eval simpl in approx zeroes 10.
Eval simpl in approx trues_falses 10.

Section map.
  Variables A B : Type.
  Variable f : A -> B .
  CoFixpoint map (s : stream A) : stream B :=
    match s with
      | Cons h t => Cons (f h) (map t)
    end.
End map.

Section interleave.
  Variable A : Type.
  CoFixpoint interleave (s1 s2 : stream A) : stream A :=
    match s1,s2 with
    | Cons h1 t1 , Cons h2 t2 => Cons h1 (Cons h2 (interleave t1 t2))
    end.
End interleave.

Definition tl A (s : stream A) : stream A :=
  match s with
  | Cons _ s' => s'
  end
.
