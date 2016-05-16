
(* 6 Subset Types and Variations *)

Require Import List Arith Cpdt.CpdtTactics.

Set Implicit Arguments.
Set Asymmetric Patters.

(* 6.1 Introducing Subset Types *)

Extraction Language Haskell.

Print pred.

Extraction "pred.hs" pred.

Lemma zgtz : 0 > 0 -> False.
               crush.
Qed.

Definition pred_strong1 (n : nat) : n > 0 -> nat :=
  match n with
  | O => fun pf : 0 > 0 => match zgtz pf with end
  | S n' => fun _ => n'
  end
.

(* Eval simpl in pred_strong1 2 . ??? *)

Theorem two_gt0 : 2 > 0.
                    crush.
Qed.

Eval compute in pred_strong1 two_gt0.

(*
Definition pred_strong1' (n : nat) (pf : n > 0) : nat :=
  match n with
  | O => match zgtz pf with end
  | S n' => n'
  end
.
 *)

Definition pred_strong1' (n : nat) : n > 0 -> nat :=
  match n return n > 0 -> nat with
  | O => fun pf : 0 > 0 => match zgtz pf with end
  | S n' => fun _ => n'
  end
.

Extraction "pred.hs" pred pred_strong1.

Print sig.

Locate "{ _ : _ | _ }".

Definition pred_strong2 (s : { n : nat | n > 0 }) : nat :=
  match s with
  | exist O pf => match zgtz pf with end
  | exist (S n') _ => n'
  end
.

Eval compute in pred_strong2 (exist _ 2 two_gt0).

Extraction "pred.hs" pred pred_strong1 pred_strong2.

Definition pred_strong3 (s : {n : nat | n > 0}) : {m : nat | proj1_sig s = S m } :=
  match s return { m : nat | proj1_sig s = S m} with
  | exist 0 pf => match zgtz pf with end
  | exist (S n') pf => exist _ n' (eq_refl _)
  end
.

Eval compute in pred_strong3 (exist _ 2 two_gt0).

Extraction "pred.hs" pred pred_strong1 pred_strong2 pred_strong3.

Definition pred_strong4 : forall n : nat, n > 0 -> {m : nat | n = S m}.
                                                     refine (fun n =>
                                                               match n with
                                                               | O => fun _ => False_rec _ _
                                                               | S n' => fun _ => exist _ n' _
                                                               end); crush.
Defined.

Print pred_strong4.

Eval compute in pred_strong4 two_gt0.

Definition pred_strong4' : forall n : nat, n > 0 -> { m : nat | n = S m}.
                                                      refine (fun n =>
                                                                match n with
                                                                | O => fun _ => False_rec _ _
                                                                | S n' => fun _ => exist _ n' _
                                                                end); abstract crush.
Defined.

Print pred_strong4'.

Notation "!" := (False_rec _ _).
Notation "[ e ]" := (exist _ e _).

Definition pred_strong5 : forall n : nat , n > 0 -> { m : nat | n = S m}.
                                                      refine (fun n =>
                                                                match n with
                                                                | O => fun _ => !
                                                                | S n' => fun _ => [n']
                                                                end); crush.
Defined.

Eval compute in pred_strong5 two_gt0.

Obligation Tactic := crush.

Program Definition pred_strong6 (n : nat) (_ : n > 0) : {m : nat | n = S m} :=
  match n with
  | O => _
  | S n' => n'
  end.

Print pred_strong6.

Eval compute in pred_strong6 two_gt0.

(* 6.2 Decidable Proposition Types *)

Print sumbool.

Notation "'Yes'" := (left _ _).
Notation "'No'"  := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

Definition eq_nat_dec : forall n m : nat , {n = m} + {n <> m}.
                                                       refine (fix f (n m : nat) : {n = m} + {n <> m} :=
                                                                 match n, m with
                                                                 | O, O => Yes
                                                                 | S n', S m' => Reduce (f n' m')
                                                                 | _, _ => No
                                                                 end); congruence.
Defined.

Eval compute in eq_nat_dec 2 2.
Eval compute in eq_nat_dec 2 3.

Definition eq_nat_dec' (n m : nat) : {n = m} + {n <> m}.
                                                 decide equality.
Defined.

Extract Inductive sumbool => "Bool" ["True" "False"].

Extraction "eq_nat_dec.hs" eq_nat_dec eq_nat_dec' .

Notation "x || y" := (if x then Yes else Reduce y).

Section In_dec.
  Variable A : Set.
  Variable A_eq_dec : forall x y : A , {x = y} + {x <> y}.
  Definition In_dec : forall (x : A) (ls : list A) , {In x ls} + {~ In x ls}.
                                                                   refine (fix f (x : A) (ls : list A) : {In x ls} + {~ In x ls} :=
                                                                             match ls with
                                                                             | nil => No
                                                                             | x' :: ls' => A_eq_dec x x' || f x ls'
                                                                             end); crush.
  Defined.
End In_dec.

Eval compute in In_dec eq_nat_dec 2 (1 :: 2 :: nil).
Eval compute in In_dec eq_nat_dec 3 (1 :: 2 :: nil).

Extraction "in_dec.hs" In_dec.

(* TODO: Extract list to haskell list... *)

(* 6.3 Partial Subset Types *)

Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A , P x -> maybe P
.

Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _).
Notation "[| x |]" := (Found _ x _).

Definition pred_strong7 : forall n : nat , {{m | n = S m}}.
                                             refine (fun n =>
                                                       match n return {{m | n = S m}} with
                                                       | O => ??
                                                       | S n' => [| n' |]
                                                       end); trivial.
Defined.

Eval compute in pred_strong7 2.
Eval compute in pred_strong7 0.

Print sumor.

Notation "!!" := (inright _ _).
Notation "[|| x ||]" := (inleft _ [x]).

Definition pred_strong8 : forall n : nat , { m : nat | n = S m } + { n = 0 }.
                                                                     refine (fun n =>
                                                                               match n with
                                                                               | O => !!
                                                                               | S n' => [|| n' ||]
                                                                               end); trivial.
Defined.

Eval compute in pred_strong8 2.
Eval compute in pred_strong8 0.
