
(* 5 Infinite Data and Proofs *)

Require Import List Cpdt.CpdtTactics.
Require Import Arith.
Set Implicit Arguments.
Set Asymmetric Patterns.

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

(* 5.2 Infinite Proofs *)

CoFixpoint ones : stream nat := Cons 1 ones.
Definition ones' := map S zeroes.

Theorem ones_eq : ones = ones'.
Abort.

Section stream_eq.
  Variable A : Type.
  CoInductive stream_eq : stream A -> stream A -> Prop :=
  | Stream_eq : forall h t1 t2,
      stream_eq t1 t2 -> stream_eq (Cons h t1) (Cons h t2).
End stream_eq.

Theorem oneS_eq : stream_eq ones ones'.
                    cofix.
Abort.

Definition frob A (s : stream A) : stream A :=
  match s with
  | Cons h t => Cons h t
  end.

Theorem frob_eq : forall A (s : stream A) , s = frob s.
                                              destruct s; reflexivity.
Qed.

Theorem ones_eq : stream_eq ones ones'.
                    cofix.
                    rewrite (frob_eq ones).
                    rewrite (frob_eq ones').
                    simpl.
                    constructor.
                    assumption.
Qed.

Theorem ones_eq' : stream_eq ones ones'.
                     cofix; crush.
                     (* Guarded ** TODO: Figure out guarded. *)
Abort.

Definition hd A (s : stream A) : A :=
  match s with
  | Cons x _ => x
  end.

Section stream_eq_coind.
  Variable A : Type.
  Variable R : stream A -> stream A -> Prop.
  Hypothesis Cons_case_hd : forall s1 s2, R s1 s2 -> hd s1 = hd s2.
  Hypothesis Cons_case_tl : forall s1 s2, R s1 s2 -> R (tl s1) (tl s2).

  Theorem stream_eq_coind : forall s1 s2 , R s1 s2 -> stream_eq s1 s2.
                                             cofix; destruct s1; destruct s2; intro.
                                             generalize (Cons_case_hd H); intro Heq; simpl in Heq; rewrite Heq.
                                             constructor.
                                             apply stream_eq_coind.
                                             apply (Cons_case_tl H).
  Qed.
End stream_eq_coind.

Print stream_eq_coind.

Theorem ones_eq'' : stream_eq ones ones'.
                      apply (stream_eq_coind (fun s1 s2 => s1 = ones /\ s2 = ones')); crush.
Qed.

Section stream_eq_loop.
  Variable A : Type.
  Variable s1 s2 : stream A.
  Hypothesis Cons_case_hd : hd s1 = hd s2.
  Hypothesis loop1 : tl s1 = s1.
  Hypothesis loop2 : tl s2 = s2.
  Theorem stream_eq_loop : stream_eq s1 s2.
                             apply (stream_eq_coind (fun s1' s2' => s1 = s1' /\ s2 = s2')); crush.
  Qed.
End stream_eq_loop.

Theorem ones_eq''' : stream_eq ones ones'.
                       apply stream_eq_loop; crush.
Qed.

Print fact.

CoFixpoint fact_slow' (n : nat) := Cons (fact n) (fact_slow' (S n)).
Definition fact_slow := fact_slow' 1.

CoFixpoint fact_iter' (cur acc : nat) := Cons acc (fact_iter' (S cur) (acc * cur)).
Definition fact_iter := fact_iter' 2 1.

Eval simpl in approx fact_iter 5.
Eval simpl in approx fact_slow 5.

Lemma fact_def : forall x n,
    fact_iter' x (fact n * S n) = fact_iter' x (fact (S n)).
      simpl; intros; f_equal; ring.
Qed.

Hint Resolve fact_def.

Lemma fact_eq' : forall n , stream_eq (fact_iter' (S n) (fact n)) (fact_slow' n).
      intro; apply (stream_eq_coind (fun s1 s2 => exists n, s1 = fact_iter' (S n) (fact n) /\ s2 = fact_slow' n)); crush; eauto.
Qed.

Theorem fact_eq : stream_eq fact_iter fact_slow.
                    apply fact_eq'.
Qed.

Section stream_eq_onequant.
  Variables A B : Type.
  Variables f g : A -> stream B.

  Hypothesis Cons_case_hd : forall x , hd (f x) = hd (g x).
  Hypothesis Cons_case_tl : forall x , exists y , tl (f x) = f y /\ tl (g x) = g y.
  Theorem stream_eq_onequant : forall x , stream_eq (f x) (g x).
        intro; apply (stream_eq_coind (fun s1 s2 => exists x , s1 = f x /\ s2 = g x)); crush; eauto.
  Qed.
End stream_eq_onequant.

Lemma fact_eq'' : forall n, stream_eq (fact_iter' (S n) (fact n)) (fact_slow' n).
      apply stream_eq_onequant; crush; eauto.
Qed.

(* 5.3 Simple Modeling of Non-Terminating Programs *)

Definition var := nat.

Definition vars := var -> nat.
Definition set (vs : vars) (v : var) (n : nat) : vars :=
  fun v' => if beq_nat v v' then n else vs v'.

Inductive exp : Set :=
| Const : nat -> exp
| Var : var -> exp
| Plus : exp -> exp -> exp
.

Fixpoint evalExp (vs : vars) (e : exp) : nat :=
  match e with
  | Const n => n
  | Var v => vs v
  | Plus e1 e2 => evalExp vs e1 + evalExp vs e2
  end
.

Inductive cmd : Set :=
| Assign : var -> exp -> cmd
| Seq : cmd -> cmd -> cmd
| While : exp -> cmd -> cmd
.

CoInductive evalCmd : vars -> cmd -> vars -> Prop :=
| EvalAssign : forall vs v e , evalCmd vs (Assign v e) (set vs v (evalExp vs e))
| EvalSeq : forall vs1 vs2 vs3 c1 c2 ,
    evalCmd vs1 c1 vs2
    -> evalCmd vs2 c2 vs3
    -> evalCmd vs1 (Seq c1 c2) vs3
| EvalWhileFalse : forall vs e c ,
    evalExp vs e = 0
    -> evalCmd vs (While e c) vs
| EvalWhileTrue : forall vs1 vs2 vs3 e c ,
    evalExp vs1 e <> 0
    -> evalCmd vs1 c vs2
    -> evalCmd vs2 (While e c) vs3
    -> evalCmd vs1 (While e c) vs3
.

(*

----------------------------------------- (EvalAssign)
{vs} Assign v e {set vs v (evalExp vs e)}

{vs1} c1 {vs2}           {vs2} c2 {vs3}
--------------------------------------- (EvalSeq)
         {vs1} Seq c1 c2 {vs3}

 evalExp vs e = 0
------------------- (EvalWhileFalse)
{vs} While e c {vs}

evalExp vs1 e <> 0     {vs1} c {vs2}      {vs2} While e c {vs3}
--------------------------------------------------------------- (EvalWhileTrue)
                   {vs1} While e c {vs3}

*)

Section evalCmd_coind.
  Variable R : vars -> cmd -> vars -> Prop.

  Hypothesis AssignCase : forall vs1 vs2 v e, R vs1 (Assign v e) vs2
    -> vs2 = set vs1 v (evalExp vs1 e).

  Hypothesis SeqCase : forall vs1 vs3 c1 c2, R vs1 (Seq c1 c2) vs3
    -> exists vs2, R vs1 c1 vs2 /\ R vs2 c2 vs3.

  Hypothesis WhileCase : forall vs1 vs3 e c, R vs1 (While e c) vs3
    -> (evalExp vs1 e = 0 /\ vs3 = vs1)
    \/ exists vs2, evalExp vs1 e <> 0 /\ R vs1 c vs2 /\ R vs2 (While e c) vs3.

  Theorem evalCmd_coind : forall vs1 c vs2, R vs1 c vs2 -> evalCmd vs1 c vs2.
    cofix; intros; destruct c.
    rewrite (AssignCase H); constructor.
    destruct (SeqCase H) as [? [? ?]]; econstructor; eauto.
    destruct (WhileCase H) as [[? ?] | [? [? [? ?]]]]; subst; econstructor; eauto.
  Qed.
End evalCmd_coind.

Fixpoint optExp (e : exp) : exp :=
  match e with
  | Plus (Const 0) e => optExp e
  | Plus e1 e2 => Plus (optExp e1) (optExp e2)
  | _ => e
  end
.

Fixpoint optCmd (c : cmd) : cmd :=
  match c with
  | Assign v e => Assign v (optExp e)
  | Seq c1 c2 => Seq (optCmd c1) (optCmd c2)
  | While e c => While (optExp e) (optCmd c)
  end
.

Lemma optExp_correct : forall vs e ,
    evalExp vs (optExp e) = evalExp vs e.
      induction e; crush;
      repeat (match goal with
              | [ |- context[match ?E with Const _ => _ | _ => _ end]] => destruct E
              | [ |- context [match ?E with O => _ | S _ => _ end ]] => destruct E
              end; crush).
Qed.

Hint Rewrite optExp_correct.

Ltac finisher :=
  match goal with
  | [ H : evalCmd _ _ _ |- _ ] => ((inversion H; [])
                                   || (inversion H; [|])); subst
  end; crush; eauto 10.

Lemma optCmd_correct1 : forall vs1 c vs2 ,
    evalCmd vs1 c vs2 -> evalCmd vs1 (optCmd c) vs2.
      intros; apply (evalCmd_coind (fun vs1 c' vs2 => exists c , evalCmd vs1 c vs2 /\ c' = optCmd c)); eauto; crush; match goal with
  | [ H : _ = optCmd ?E |- _ ] => destruct E; simpl in *; discriminate || injection H; intros; subst
                                                                                                                     end; finisher.
Qed.

Lemma optCmd_correct2 : forall vs1 c vs2 ,
    evalCmd vs1 (optCmd c) vs2 -> evalCmd vs1 c vs2.
      intros; apply (evalCmd_coind (fun vs1 c vs2 => evalCmd vs1 (optCmd c) vs2));
      crush; finisher.
Qed.

Theorem optCmd_correct : forall vs1 c vs2 ,
    evalCmd vs1 (optCmd c) vs2 <-> evalCmd vs1 c vs2.
      intuition; apply optCmd_correct1
                 || apply optCmd_correct2; assumption.
Qed.
