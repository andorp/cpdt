
Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.

(* Source Language *)

Inductive type : Set := Nat | Bool.

Inductive binop : type -> type -> type -> Set :=
| Plus : binop Nat Nat Nat
| Times : binop Nat Nat Nat
| Eq : forall t , binop t t Bool
| Lt : binop Nat Nat Bool
.

Inductive exp : type -> Set :=
| NConst : nat -> exp Nat
| BConst : bool -> exp Bool
| Binop : forall t1 t2 t , binop t1 t2 t -> exp t1 -> exp t2 -> exp t
.

Definition typeDenote (t: type) : Set :=
  match t with
  | Nat => nat
  | Bool => bool
  end
.

Definition binopDenote arg1 arg2 res (b: binop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
  | Plus => plus
  | Times => mult
  | Eq Nat => beq_nat
  | Eq Bool => eqb
  | Lt => leb
  end
.

Fixpoint expDenote t (e : exp t) : typeDenote t :=
  match e with
  | NConst n => n
  | BConst b => b
  | Binop _ _ _ b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end
.

(* Target langauge *)

Definition tstack := list type.

(* Define an indexed type family, which captures the relation between well
   defined stacks *)
Inductive instr : tstack -> tstack -> Set :=
| INConst : forall s , nat -> instr s (Nat :: s)
| IBConst : forall s , bool -> instr s (Bool :: s)
| IBinop : forall arg1 arg2 res s ,
    binop arg1 arg2 res -> instr (arg1 :: arg2 :: s) (res :: s)
.

Inductive prog : tstack -> tstack -> Set :=
| Nil : forall s , prog s s
| Cons : forall s1 s2 s3 ,
    instr s1 s2 -> prog s2 s3 -> prog s1 s3
.

Fixpoint vstack (ts : tstack) : Set :=
  match ts with
  | nil => unit
  | t :: ts' => typeDenote t * vstack ts'
  end % type (* %type means parse as a type *)
.

Definition instrDenote ts ts' (i : instr ts ts') : vstack ts -> vstack ts' :=
  match i with
  | INConst _ n => fun s => (n, s)
  | IBConst _ b => fun s => (b, s)
  | IBinop _ _ _ _ b => fun s =>
                          let '(arg1, (arg2, s')) := s in
                          ((binopDenote b) arg1 arg2, s')
  end
.

Fixpoint progDenote ts ts' (p : prog ts ts') : vstack ts -> vstack ts' :=
  match p with
  | Nil _ => fun s => s
  | Cons _ _ _ i p' => fun s => progDenote p' (instrDenote i s)
  end
.

Fixpoint concat ts ts' ts'' (p : prog ts ts') : prog ts' ts'' -> prog ts ts'' :=
  match p with
  | Nil _ => fun p' => p'
  | Cons _ _ _ i p1 => fun p' => Cons i (concat p1 p')
  end
.

Fixpoint compile t (e : exp t) (ts : tstack) : prog ts (t :: ts) :=
  match e with
  | NConst n => Cons (INConst _ n) (Nil _)
  | BConst b => Cons (IBConst _ b) (Nil _)
  | Binop _ _ _ b e1 e2 =>
    concat (compile e2 _)
           (concat (compile e1 _) (Cons (IBinop _ b) (Nil _)))
  end
.

Lemma compile_correct' : forall t (e : exp t) ts (s : vstack ts) ,
    progDenote (compile e ts) s = (expDenote e, s)
.

induction e; crush.

Abort.

Lemma concat_correct : forall ts ts' ts'' (p : prog ts ts') (p' : prog ts' ts'') (s : vstack ts) ,
    progDenote (concat p p') s = progDenote p' (progDenote p s)
.
    induction p; crush.
Qed.

Hint Rewrite concat_correct.

Lemma compile_correct' : forall t (e : exp t) ts (s : vstack ts),
    progDenote (compile e ts) s = (expDenote e, s).
    induction e; crush.
Qed.

Hint Rewrite compile_correct'.

Theorem compile_correct : forall t (e : exp t),
    progDenote (compile e nil) tt = (expDenote e, tt).
    crush.
Qed.

Extraction compile.

