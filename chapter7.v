
(* 7 General Recursion *)

Require Import List Arith Cpdt.CpdtTactics.

Set Implicit Arguments.
Set Asymetric Patterns.

Extraction Language Haskell.

(* 7.1 Well-Founded Recursion *)

Section stream.
  Variable A : Type.
  CoInductive stream : Type :=
  | Cons : A -> stream -> stream
  .
End stream.


Section mergeSort.
  Variable A : Type.
  Variable le : A -> A -> bool.

  Fixpoint insert (x : A) (ls : list A) : list A :=
    match ls with
    | nil => x :: nil
    | h :: ls' =>
      if le x h
      then x :: ls
      else h :: insert x ls'
    end.

  Fixpoint merge (ls1 ls2 : list A) : list A :=
    match ls1 with
    | nil => ls2
    | h :: ls' => insert h (merge ls' ls2)
    end.

  Fixpoint split (ls : list A) : list A * list A :=
    match ls with
    | nil => (nil, nil)
    | h :: nil => (h :: nil, nil)
    | h1 :: h2 :: ls' =>
      let (ls1, ls2) := split ls' in
      (h1 :: ls1, h2 :: ls2)
    end.

  (*
  Fixpoint mergeSort (ls : list A) : list A :=
    if leb (length ls) 1
    then ls
    else let lss := split ls in
         merge (mergeSort (fst lss)) (mergeSort (snd lss)).
   *)

  Print well_founded.
  Print Acc.
  
  CoInductive infiniteDecreasingChain A (R : A -> A -> Prop) : stream A -> Prop :=
  | ChainCons : forall x y s , infiniteDecreasingChain R (Cons y s)
                               -> R y x
                               -> infiniteDecreasingChain R (Cons x (Cons y s)).

  Lemma noBadChains' : forall A (R : A -> A -> Prop) x , Acc R x
                                                         -> forall s , ~infiniteDecreasingChain R (Cons x s).
          induction 1; crush;
          match goal with
          | [ H : infiniteDecreasingChain _ _ |- _ ] => inversion H; eauto
          end.
  Qed.

  Theorem noBadChains : forall A (R : A -> A -> Prop) , well_founded R
                                                        -> forall s , ~infiniteDecreasingChain R s .
          destruct s; apply noBadChains'; auto.
  Qed.

  Check Fix.

  Definition lengthOrder (ls1 ls2 : list A) :=
    length ls1 < length ls2.

  Hint Constructors Acc.

  Lemma lengthOrder_wf' : forall len ls , length ls <= len -> Acc lengthOrder ls.
                                           unfold lengthOrder; induction len; crush.
  Defined.

  Theorem lengthOrder_wf : well_founded lengthOrder.
                             red.
                             intro.
                             eapply lengthOrder_wf'.
                             eauto.
  Defined.

  Lemma split_wf : forall len ls , 2 <= length ls <= len
                                   -> let (ls1, ls2) := split ls in
                                      lengthOrder ls1 ls /\ lengthOrder ls2 ls.
  unfold lengthOrder; induction len; crush; do 2 (destruct ls; crush);
  destruct (le_lt_dec 2 (length ls));
  repeat (match goal with
          | [ _ : length ?E < 2 |- _ ] => destruct E
          | [ _ : S (length ?E) < 2 |- _ ] => destruct E
          | [ IH : _ |- context[split ?L] ] => specialize (IH L); destruct (split L); destruct IH
          end; crush).
   Defined.

  Ltac split_wf := intros ls ?; intros; generalize (@split_wf (length ls) ls);
                   destruct (split ls); destruct 1; crush.

  Lemma split_wf1 : forall ls , 2 <= length ls -> lengthOrder (fst (split ls)) ls.
                                  split_wf.
  Defined.

  Lemma split_wf2 : forall ls , 2 <= length ls -> lengthOrder (snd (split ls)) ls.
                                  split_wf.
  Defined.

  Hint Resolve split_wf1 split_wf2.

  Definition mergeSort : list A -> list A.
                           refine (Fix lengthOrder_wf (fun _ => list A)
                                       (fun (ls : list A)
                                            (mergeSort : forall ls' : list A , lengthOrder ls' ls -> list A) =>
                                          if le_lt_dec 2 (length ls)
                                          then let lss := split ls in
                                               merge (mergeSort (fst lss) _) (mergeSort (snd lss) _)
                                          else ls));
    subst lss;
    eauto.
  Defined.
End mergeSort.

Eval compute in mergeSort leb (1 :: 2 :: 36 :: 8 :: 19 :: nil).

Theorem mergeSort_eq : forall A (le : A -> A -> bool) ls ,
    mergeSort le ls = if le_lt_dec 2 (length ls)
                      then let lss := split ls in
                           merge le (mergeSort le (fst lss)) (mergeSort le (snd lss))
                      else ls.
                          intros; apply (Fix_eq (@lengthOrder_wf A) (fun _ => list A)); intros.
                          
                          Check Fix_eq.
                          match goal with
                          | [ |- context[match ?E with left _ => _ | right _ => _ end] ] => destruct E
                          end; simpl; f_equal; auto.
Qed.

Extraction "mergeSort.hs" mergeSort.

Check well_founded_induction.

