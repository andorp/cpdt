
(* 4 Inductive Predicates *)

Require Import Cpdt.CpdtTactics.
Require Import List.

Print unit.

Print True.

(* 4.1 Propositional Logic *)

Section Propositional.
  Variables P Q R : Prop.

  Theorem obvious :
    True.
      apply I.
  Qed.

  Theorem obvious' :
    True.
      constructor.
  Qed.

  Print False.

  Theorem False_imp : False -> 2 + 2 = 5.
                                 destruct 1.
  Qed.

  Theorem ariyh_neq : 2 + 2 = 5 -> 9 + 9 = 835.
                                     intro.
                                     elimtype False.
                                     crush.
  Qed.

  Print not.

  Theorem arith_neq' : ~(2 + 2 = 5).
                         unfold not.
                         crush.
  Qed.

  Print and.

  Theorem and_comm : P /\ Q -> Q /\ P .
                                 destruct 1.
                                 split.
                                 assumption.
                                 assumption.
  Qed.

  Print or.

  Theorem or_comm : P \/ Q -> Q \/ P.
                                destruct 1.
                                right.
                                assumption.
                                left.
                                assumption.
  Qed.

  Theorem or_comm' : P \/ Q -> Q \/ P.
                                 tauto.
  Qed.

  Theorem arith_comm : forall ls1 ls2 : list nat ,
      length ls1 = length ls2 \/ length ls1 + length ls2 = 6
      -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
                                      intuition.
                                      rewrite app_length.
                                      tauto.
  Qed.

  Theorem arith_comm' : forall ls1 ls2 : list nat ,
      length ls1 = length ls2 \/ length ls1 + length ls2 = 6
      -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
                                      Hint Rewrite app_length.
                                      crush.
  Qed.

End Propositional.

(* 4.2 What Does It Mean to Be Constructive? *)

(* 4.3 First-Order Logic *)

Print ex.

Theorem exist1 : exists x : nat , x + 1 = 2.
                                    exists 1.
                                    reflexivity.
Qed.

Theorem exist2 : forall n m : nat , (exists x : nat , n + x = m) -> n <= m.
                                                                      destruct 1.
                                                                      crush.
Qed.

(* 4.4 Predicates with Implicit Equality *)

Inductive isZero : nat -> Prop :=
| IsZero : isZero 0
.

Theorem isZero_zero : isZero 0.
                        constructor.
Qed.

(*
This can be interpreted as a Judgement, or natural deduction rule.

-------- (IsZero)
isZero 0

 *)

Print eq.

(*
Another way of stating that definition is: equality is defined
as the least reflexive relation.
*)

Theorem isZero_plus : forall n m : nat , isZero m -> n + m = n.
                                                       destruct 1.
                                                       crush.
Qed.

Theorem isZero_contra : isZero 1 -> False.
                          destruct 1.
                          Undo.
                          inversion 1.
Qed.

Theorem isZero_contra' : isZero 1 -> 2 + 2 = 5.
                                       destruct 1.
Abort.

Check isZero_ind.

(* 4.5 Recursive Predicates *)

Inductive even : nat -> Prop :=
| EvenO : even O
| EvenSS : forall n , even n -> even (S (S n))
.

(*
Natural deduction rules:

------ (EvenO)
even 0


    even n
-------------- (EvenSS)
even (S (S n))

*)

Theorem even_O : even 0.
                   constructor.
Qed.

Theorem even_4 : even 4.
                   constructor.
                   constructor.
                   constructor.
Qed.

Hint Constructors even.

Theorem even_4' : even 4.
                    auto.
Qed.

Theorem even_1_contra : even 1 -> False.
                          inversion 1.
Qed.

Theorem even_3_contra : even 3 -> False.
                          inversion 1.
                          inversion H1.
Qed.

Theorem even_plus : forall n m, even n -> even m -> even (n + m).
                                  induction n; crush.
                                  inversion H.
                                  simpl.
                                  constructor.
                                  Restart.
                                  induction 1.
                                  crush.
                                  intro.
                                  simpl; constructor.
                                  apply IHeven; assumption.
                                  Restart.
                                  induction 1; crush.
Qed.

Theorem even_contra : forall n , even (S (n + n)) -> False.
                                   induction 1.
Abort.

Lemma even_contra' : forall n' , even n' -> forall n, n' = S (n + n) -> False.
                                                        induction 1; crush.
                                                        destruct n; destruct n0; crush.
                                                        SearchRewrite (_ + S _).
                                                        rewrite <- plus_n_Sm in H0.
                                                        apply IHeven with n0; assumption.
                                                        Restart.
                                                        Hint Rewrite <- plus_n_Sm.
                                                        induction 1;crush;
                                                        match goal with
                                                        | [ H : S ?N = ?N0 + ?N0 |- _ ] => destruct N; destruct N0
                                                        end; crush.
Qed.

Theorem even_contra : forall n , even (S (n + n)) -> False.
                                   intros; eapply even_contra'; eauto.
Qed.
