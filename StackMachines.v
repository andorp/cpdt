
(* Source langauge *)

Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive binop : Set := Plus | Times.

Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

Definition binopDenote (b: binop) : nat -> nat -> nat :=
  match b with
  | Plus => plus
  | Times => mult
  end.

Fixpoint expDenote(e: exp): nat :=
  match e with
  | Const n => n
  | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.

(* Examples *)

Eval simpl in expDenote (Const 42).

Eval simpl in expDenote (Binop Plus (Const 2) (Const 2)).

Eval simpl in expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

(* Target Language *)

Inductive instr : Set :=
| iConst : nat -> instr
|iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

Definition instrDenote (i: instr) (s: stack) : option stack :=
  match i with
  | iConst n => Some (n :: s)
  | iBinop b =>
    match s with
    | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
    | _ => None
    end
  end.

Fixpoint progDenote(p: prog) (s: stack) : option stack :=
  match p with
  | nil => Some s
  | i :: p' =>
    match instrDenote i s with
    | None => None
    | Some s' => progDenote p' s'
    end
  end.

(* Translation *)

Fixpoint compile (e: exp) : prog :=
  match e with
  | Const n => iConst n :: nil
  | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
  end.

Eval simpl in compile (Const 42).
Eval simpl in compile (Binop Plus (Const 2) (Const 2)).
Eval simpl in compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

Eval simpl in progDenote (compile (Const 42)) nil.
Eval simpl in progDenote (compile (Binop Plus (Const 2) (Const 2))) nil.
Eval simpl in progDenote (compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))) nil.

(* Correctness proof *)

Theorem compile_correct : forall e , progDenote (compile e) nil = Some (expDenote e :: nil).

Abort.

(* Trick: Strengtening the induction hypothesis *)

Lemma compile_correct' : forall e p s ,
    progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).

(* First subgoal *)
induction e.
intros.
unfold compile.
unfold expDenote.
unfold progDenote at 1.
simpl.
fold progDenote.
reflexivity.

intros.
unfold compile.
fold compile.
unfold expDenote.
fold expDenote.

Check app_assoc_reverse.
SearchRewrite ((_ ++ _) ++ _).

rewrite app_assoc_reverse.
rewrite IHe2.

rewrite app_assoc_reverse.
rewrite IHe1.

unfold progDenote at 1.
simpl.
fold progDenote.
reflexivity.

Abort.

(* Automatic reasoning *)

Lemma compile_correct'' : forall e s p, progDenote (compile e ++ p) s =
  progDenote p (expDenote e :: s).
  induction e; crush.
Qed.

Theorem compile_correct : forall e , progDenote (compile e) nil = Some (expDenote e :: nil).

intros.

Check app_nil_end.

rewrite (app_nil_end (compile e)).
rewrite compile_correct''.
reflexivity.
Qed.
