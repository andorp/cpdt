
(* 6 Subset Types and Variations *)

Require Import Arith Cpdt.CpdtTactics.

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
