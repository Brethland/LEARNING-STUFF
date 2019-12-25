(* A Simple Data Structure Lemma *)

Require Import Omega.
Inductive BTree : Type :=
    Leaf        : BTree
  | Single_Son  : BTree -> BTree
  | Binary_Sons : BTree -> BTree -> BTree.

Fixpoint empty_place (t : BTree) : nat :=
  match t with
  | Leaf              => 2
  | Single_Son t'     => 1 + empty_place t'
  | Binary_Sons t1 t2 => empty_place t1 + empty_place t2
  end.

Fixpoint node (t : BTree) : nat :=
  match t with
  | Leaf              => 1
  | Single_Son t'     => 1 + node t'
  | Binary_Sons t1 t2 => 1 + node t1 + node t2
  end.

Lemma l : forall t n, node t = n -> empty_place t = n + 1.
Proof.
  induction t;intros.
  - simpl in *. subst. auto.
  - simpl in *. destruct n.
    + inversion H.
    + assert(H' : node t = n).
      auto. apply IHt in H'. rewrite H'. auto.
  - simpl in *. destruct n.
    + inversion H.
    + assert(H' : node t1 + node t2 = n).
      auto. specialize (IHt1 (node t1)).
      specialize (IHt2 (node t2)).
      assert(H1 : node t1 = node t1). auto.
      assert(H2 : node t2 = node t2). auto.
      apply IHt1 in H1. apply IHt2 in H2.
      rewrite H1, H2. omega.
Qed.

Require Import Lia ssreflect.

Lemma k : forall t n, node t = n -> empty_place t = n + 1.
Proof.
  elim => /= [| t1 IH | t1 IH1 t2 IH2] n.
  + by move => <-.
  + by case: n => // n [/IH] ->.
  + case: n => // n [eq].
    have/IH1 ->: node t1 = n - node t2 by lia.
    by move: (IH2 _ eq_refl); lia.
Qed.