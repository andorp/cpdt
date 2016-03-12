(* 3 Introducing Inductive Types *)

Require Import Cpdt.CpdtTactics.
Set Implicit Arguments.

(* 3.1 Proof Terms *)

Check (fun x : nat => x).

Check (fun x : True => x).

Check I.

Check (fun _ : False => I).

Check (fun x : False => x).

(* 3.2 Enumerations *)

Inductive unit : Set :=
| tt
.

Check unit.
Check tt.

(* We can prove that unit is a genuine singleton type. *)

Theorem unit_singleton : forall x : unit, x = tt.

induction x.
reflexivity.
Qed.

Check unit_ind.

Inductive Empty_set : Set := .

Theorem the_sky_is_falling : forall x : Empty_set, 2 + 2 = 5.
   destruct 1.
Qed.

Check Empty_set_ind.

Definition e2u (e : Empty_set) : unit := match e with end.

Inductive bool : Set :=
| true
| false
.

Definition negb (b :  bool) : bool :=
  match b with
  | true => false
  | false => true
  end
.

Definition negb' (b : bool) : bool :=
  if b then false else true
.

Definition negb'' (b : bool) : _ :=
  if b then false else true
.

Theorem negb_inverse : forall b : bool , negb (negb b) = b.
  destruct b; reflexivity.
Qed.

Theorem negb_inqe : forall b : bool, negb b <> b.
  destruct b; discriminate.
Qed.

Check bool_ind.

(* 3.3 Simple Recursive Types *)

Inductive nat : Set :=
| O : nat
| S : nat -> nat
.

Definition isZero (n : nat) : bool :=
  match n with
  | O => true
  | S _ => false
  end
.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end
.

Check pred.

Fixpoint plus n m :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end
.

Check plus.

Theorem O_plus_n : forall n : nat , plus O n = n.
  intro; reflexivity.
Qed.

Theorem n_plus_O : forall n : nat , plus n O = n.
                                      induction n.
                                      reflexivity.
                                      simpl.
                                      rewrite IHn.
                                      reflexivity.
Qed.

Theorem n_plus_O' : forall n : nat , plus n O = n.
  induction n; crush.
Qed.

Check nat_ind.

Theorem S_inj : forall n m : nat , S n = S m -> n = m.
  injection 1; trivial.
Qed.

(* Haskell extraction of a given function *)
Extraction Language Haskell.
Extraction "arith.hs" plus.

Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list
.

Fixpoint nlength (ls : nat_list) : nat :=
  match ls with
  | NNil => O
  | NCons _ ls' => S (nlength ls')
  end
.

Fixpoint napp (ls1 ls2 : nat_list) : nat_list :=
  match ls1 with
  | NNil => ls2
  | NCons n ls1' => NCons n (napp ls1' ls2)
  end
.

Theorem nlength_app : forall ls1 ls2 : nat_list ,
    nlength (napp ls1 ls2) = plus (nlength ls1) (nlength ls2).
      induction ls1; crush.
Qed.

Check nat_list_ind.

Inductive nat_btree : Set :=
| Leaf : nat_btree
| Node : nat_btree -> nat -> nat_btree -> nat_btree
.

Fixpoint size (tr : nat_btree) : nat :=
  match tr with
  | Leaf => S O
  | Node tr1 _ tr2 => plus (size tr1) (size tr2)
  end
.

Fixpoint splice (tr1 tr2 : nat_btree) : nat_btree :=
  match tr1 with
  | Leaf => Node tr2 O Leaf
  | Node tr1' n tr2' => Node (splice tr1' tr2) n tr2'
  end
.

Theorem plus_assoc : forall n1 n2 n3 : nat ,
    plus (plus n1 n2) n3 = plus n1 (plus n2 n3).
      induction n1; crush.
Qed.

Hint Rewrite n_plus_O plus_assoc.

Theorem size_splice : forall tr1 tr2 : nat_btree ,
    size (splice tr1 tr2) = plus (size tr2) (size tr1).
      induction tr1; crush.
Qed.

Check nat_btree_ind.

(* 3.4 Parameterized Types *)

(* Without section 
Inductive list (T : Set) : Set :=
| Nil : list T
| Cons : T -> list T -> list T
.

Fixpoint length T (ls : list T) : nat :=
  match ls with
  | Nil => O
  | Cons _ ls' => S (length ls')
  end
.

(* Without implicit arguments
Fixpoint length T (ls : list T) : nat :=
  match ls with
  | Nil => O
  | Cons _ ls' => S (length _ ls')
  end
.
*)

Fixpoint app T (ls1 ls2 : list T) : list T :=
  match ls1 with
  | Nil => ls2
  | Cons x ls1' => Cons x (app ls1' ls2)
  end
.

Theorem length_app : forall T (ls1 ls2 : list T) ,
    length (app ls1 ls2) = plus (length ls1) (length ls2).
      induction ls1; crush.
Qed.
*)

Section list.
  Variable T : Set.

  Inductive list : Set :=
  | Nil : list
  | Cons : T -> list -> list
  .

  Fixpoint length (ls : list) : nat :=
    match ls with
    | Nil => O
    | Cons _ ls' => S (length ls')
    end.

  Fixpoint app (ls1 ls2 : list) : list :=
    match ls1 with
    | Nil => ls2
    | Cons x ls1' => Cons x (app ls1' ls2)
    end.

  Theorem length_app : forall ls1 ls2 : list,
      length (app ls1 ls2) = plus (length ls1) (length ls2).
        induction ls1; crush.
  Qed.
End list.

(*
Implicit Arguments Nil [T].
Warning: Implicit Arguments is deprecated; use Arguments instead
*)

Arguments Nil [T].

Print list.

Check length.

Check list_ind.

(* 3.5 Mutually Inductive Types *)

Inductive even_list : Set :=
| ENil : even_list
| ECons : nat -> odd_list -> even_list

with odd_list : Set :=
| OCons : nat -> even_list -> odd_list
.

Fixpoint elength (el : even_list) : nat :=
  match el with
  | ENil => O
  | ECons _ ol => S (olength ol)
  end

with olength (ol : odd_list) : nat :=
  match ol with
  | OCons _ el => S (elength el)
  end
.

Fixpoint eapp (el1 el2 : even_list) : even_list :=
  match el1 with
  | ENil => el2
  | ECons n ol => ECons n (oapp ol el2)
  end

with oapp (ol : odd_list) (el : even_list) : odd_list :=
  match ol with
  | OCons n el' => OCons n (eapp el' el)
  end
.
(*
Theorem elength_eapp : forall el1 el2 : even_list ,
    elength (eapp el1 el2) = plus (elength el1) (elength el2).
      induction el1; crush.
Abort.
*)
Check even_list_ind.

Scheme even_list_mut := Induction for even_list Sort Prop
with odd_list_mut := Induction for odd_list Sort Prop
.

Check even_list_mut.

Theorem elength_eapp : forall el1 el2 : even_list ,
    elength (eapp el1 el2) = plus (elength el1) (elength el2).
      apply (even_list_mut
               (fun el1 : even_list => forall el2 : even_list,
                    elength (eapp el1 el2) = plus (elength el1) (elength el2))
               (fun ol : odd_list => forall el : even_list,
                    olength (oapp ol el) = plus (olength ol) (elength el))); crush.
Qed.

