(*
CoInductive free (F : Type -> Type) (X : Type) : Type :=
  | pure : X -> free F X
  | roll : F (free F X) -> free F X.
*)

(* https://sympa.inria.fr/sympa/arc/coq-club/2014-10/msg00035.html *)
Record Signature (I : Type) : Type := 
{
  Operations : I -> Type;
  Arities : forall i : I, Operations i -> Type;
  Sorts : forall i : I, forall op : Operations i, Arities i op -> I 
}.
Arguments Operations [_] _ i.
Arguments Arities [_] _ [_] op.
Arguments Sorts [_] _ [_] [_] ar.

Inductive list (X : Type) : Type :=
  | nil : list X
  | cons (x : X) (xs : list X).

(* Type Annotation Inference *)
Fixpoint repeat X x count : list X :=
  match count with
    | 0 => nil X
    | S count' => cons X x (repeat X x count')
  end.

Check nil.
Check (cons nat 2 (cons nat 1 (nil nat))).

Arguments nil {_}.
Arguments cons {_}.
Arguments repeat {_}.

Check repeat 3 3.
Check cons 3 nil.

Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
  match l1 with
    | nil => l2
    | cons h t => cons h (app t l2)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
    | nil => 0
    | cons _ l' => S (length l')
  end.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Check app.
Check 3 :: 2 :: 1 :: nil.

Theorem app_nil_r : forall (X : Type), forall l : list X,
  l ++ [] = l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros.
  induction l.
  - simpl.
    auto.
  - simpl.
    rewrite <- IHl.
    auto.
Qed.

Lemma app_length : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1.
  - simpl.
    auto.
  - simpl.
    rewrite <- IHl1.
    auto.
Qed.

Inductive tuple2 (X Y : Type) : Type :=
  | pair (p : X) (q : Y) : tuple2 X Y.

Arguments tuple2 {_} {_}.