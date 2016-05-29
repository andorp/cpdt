
(* 7 General Recursion *)

Require Import Bool List Arith Cpdt.CpdtTactics Cpdt.Coinductive.


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

(* 7.2 A Non-TErmination Monad Insipred by Domain Theory *)

Section computation.
  Variable A : Type.
  Definition computation := { f : nat -> option A | forall (n : nat) (v : A) ,
                                f n = Some v -> forall (n' : nat), n' >= n -> f n' = Some v }.
  Definition runTo (m : computation) (n : nat) (v : A) :=
    proj1_sig m n = Some v.

  Definition run (m : computation) (v : A) :=
    exists n , runTo m n v.
End computation.

Hint Unfold runTo.

Ltac run' := unfold run, runTo in *; try red; crush;
  repeat (match goal with
            | [ _ : proj1_sig ?E _ = _ |- _ ] =>
              match goal with
                | [ x : _ |- _ ] =>
                  match x with
                    | E => destruct E
                  end
              end
            | [ |- context[match ?M with exist _ _ => _ end] ] => let Heq := fresh "Heq" in
              case_eq M; intros ? ? Heq; try rewrite Heq in *; try subst
            | [ _ : context[match ?M with exist _ _ => _ end] |- _ ] => let Heq := fresh "Heq" in
              case_eq M; intros ? ? Heq; try rewrite Heq in *; subst
            | [ H : forall n v, ?E n = Some v -> _,
                _ : context[match ?E ?N with Some _ => _ | None => _ end] |- _ ] =>
              specialize (H N); destruct (E N); try rewrite (H _ (eq_refl _)) by auto; try discriminate
            | [ H : forall n v, ?E n = Some v -> _, H' : ?E _ = Some _ |- _ ] => rewrite (H _ _ H') by auto
          end; simpl in *); eauto 7.

Ltac run := run'; repeat (match goal with
                            | [ H : forall n v, ?E n = Some v -> _
                                |- context[match ?E ?N with Some _ => _ | None => _ end] ] =>
                              specialize (H N); destruct (E N); try rewrite (H _ (eq_refl _)) by auto; try discriminate
                          end; run').

Lemma ex_irrelevant : forall P : Prop, P -> exists n : nat, P.
  exists 0; auto.
Qed.

Hint Resolve ex_irrelevant.

Require Import Max.

Theorem max_spec_le : forall n m, n <= m /\ max n m = m \/ m <= n /\ max n m = n.
  induction n; destruct m; simpl; intuition;
    specialize (IHn m); intuition.
Qed.

Ltac max := intros n m; generalize (max_spec_le n m); crush.

Lemma max_1 : forall n m, max n m >= n.
  max.
Qed.

Lemma max_2 : forall n m, max n m >= m.
  max.
Qed.

Hint Resolve max_1 max_2.

Lemma ge_refl : forall n, n >= n.
  crush.
Qed.

Hint Resolve ge_refl.

Hint Extern 1 => match goal with
                   | [ H : _ = exist _ _ _ |- _ ] => rewrite H
                 end.

Section Bottom.
  Variable A : Type.
  Definition Bottom : computation A.
                        exists (fun _ : nat => @None A); abstract run.
  Defined.

  Theorem run_Bottom : forall v , ~run Bottom v.
        run.
  Qed.
End Bottom.

Section Return.
  Variable A : Type.
  Variable v : A.
  Definition Return : computation A.
                        intros; exists (fun _ : nat => Some v); abstract run.
  Defined.

  Theorem run_Return : run Return v.
                         run.
  Qed.
End Return.

Section Bind.
  Variable A B : Type.
  Variable m1 : computation A.
  Variable m2 : A -> computation B.
  Definition Bind : computation B.
                      exists (fun n =>
                                let (f1, _) := m1 in
                                match f1 n with
                                | None => None
                                | Some v => let (f2, _) := m2 v in
                                            f2 n
                                end); abstract run.
  Defined.

  Theorem run_Bind : forall (v1 : A) (v2 : B) ,
      run m1 v1 -> run (m2 v1) v2
      -> run Bind v2.
        run; match goal with
             | [ x : nat , y : nat |- _ ] => exists (max x y)
             end; run.
  Qed.
End Bind.

Notation "x <- m1 ; m2" :=
  (Bind m1 (fun x => m2)) (right associativity, at level 70).

Definition meq A (m1 m2 : computation A) := forall n , proj1_sig m1 n = proj1_sig m2 n.

Theorem left_identity : forall A B (a : A) (f : A -> computation B) ,
    meq (Bind (Return a) f) (f a).
      run.
Qed.

Theorem right_identity : forall A (m : computation A) ,
    meq (Bind m (@Return _)) m.
      run.
Qed.

Theorem associativity : forall A B C (m : computation A)
                               (f : A -> computation B) (g : B -> computation C) ,
    meq (Bind (Bind m f) g) (Bind m (fun x => Bind (f x) g)).
      run.
Qed.

Section lattice.
  Variable A : Type.
  Definition leq (x y : option A) :=
    forall v , x = Some v -> y = Some v.
End lattice.

Section Fix.
  Variables A B : Type.
  Variable f : (A -> computation B) -> (A -> computation B).

  Hypothesis f_continuous : forall n v v1 x , runTo (f v1 x) n v
                                              -> forall (v2 : A -> computation B),
        (forall x , leq (proj1_sig (v1 x) n) (proj1_sig (v2 x) n)) -> runTo (f v2 x) n v.

  Fixpoint Fix' (n : nat) (x : A) : computation B :=
    match n with
    | O => Bottom _
    | S n' => f (Fix' n') x
    end.

  Hint Extern 1 (_ >= _) => omega.
  Hint Unfold leq.

  Lemma Fix'_ok : forall steps n x v , proj1_sig (Fix' n x) steps = Some v
                                       -> forall n' , n' >= n -> proj1_sig (Fix' n' x) steps = Some v.
                                                                   unfold runTo in *; induction n; crush;
                                                                   match goal with
                                                                   | [ H : _ >= _ |- _ ] => inversion H; crush; eauto
                                                                   end.
  Qed.
  