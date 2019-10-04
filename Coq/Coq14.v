(*
  Exercises for <Software Foundations> CH7.
  Author : Brethland, Late 2019.
*)

From Coq Require Import Nat.
From Coq Require Import Unicode.Utf8.
Require Import Setoid.
Require Import PeanoNat.
Require Import Peano.
Require Import Arith.
Require Import List.

Inductive reflect (P : Prop) : bool → Prop := 
  | ReflectT : P → reflect P true 
  | ReflectF : ¬ P → reflect P false.

Theorem iff_reflect : ∀ P b, (P ↔ b = true) → reflect P b. 
Proof. 
  intros P b H. destruct b.   
  - apply ReflectT. rewrite H. reflexivity.   
  - apply ReflectF. rewrite H. intros H'. inversion H'. 
Qed.

Theorem reflect_iff : ∀ P b, reflect P b → (P ↔ b = true). 
Proof.
  intros. split.
  - destruct H.
    + auto.
    + intros. unfold not in H. apply H in H0. inversion H0.
  - destruct H.
    + auto.
    + intros. inversion H0.
Qed.

Lemma beq_natP : ∀ n m, reflect (n = m) (beq_nat n m). 
Proof.   
  intros n m. apply iff_reflect. rewrite beq_nat_true_iff. reflexivity. 
Qed.

Notation "x :: l" := (cons x l)
                      (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Fixpoint count n l :=   
  match l with   
  | [] => 0   
  | m :: l' => (if beq_nat n m then 1 else 0) + count n l'   
  end.

Theorem beq_natP_practice : ∀ n l,   count n l = 0 → ~(In n l). 
Proof.
  intros n l. induction l.
  - intros. unfold not. intros. inversion H0.
  - simpl. intros. destruct (beq_natP n a) as [H1 | H1].
    + inversion H.
    + unfold not.
      intros. destruct H0.
      ++ destruct H1. auto.
      ++ apply IHl in H. destruct H. auto.
Qed.

Inductive nostutter {X:Type} : list X → Prop := 
  | EmptyStutter : nostutter []
  | Onestutter : forall (a : X), nostutter [a]
  | ConsStutter : forall (a b: X) (l : list X), nostutter (b :: l) -> a <> b -> nostutter (a :: b :: l).

Example test_nostutter_4: not (nostutter [3;1;1;4]). 
Proof.
  Proof. intro.   
  repeat match goal with     
         h: nostutter _ |- _ => inversion h; clear h; subst   
         end.   
  contradiction H5; 
  auto.
Qed.

Lemma cons_inj : forall {X} (a : X) (l1 l2 : list X), l1 = l2 -> a :: l1 = a :: l2.
Proof.
  intros. rewrite H. auto.
Qed.

Inductive in_order_merge {X : Type} : list X -> list X -> list X -> Prop :=
  | EmptyMerge : in_order_merge [] [] []
  | ConsMergeL : forall (a : X) (l l1 l2 : list X), in_order_merge l l1 l2
                                                  -> in_order_merge (a :: l) (a :: l1) l2
  | ConsMergeR : forall (a : X) (l l1 l2 : list X), in_order_merge l l1 l2
                                                  -> in_order_merge (a :: l) l1 (a :: l2).

Lemma filter_correct : forall {X} (l l1 l2 : list X) (test: X -> bool),
  in_order_merge l l1 l2 -> (forall x : X, In x l1 -> test x = true)
  -> (forall x : X, In x l2 -> test x = false) -> filter test l = l1.
Proof.
  intros X l. induction l.
  - intros. inversion H. auto.
  - intros. inversion H.
    + assert(H' : In a l1).
      rewrite <- H3. simpl. left. auto.
      apply H0 in H'. simpl. rewrite H'.
      apply cons_inj. apply IHl with (l2:=l4).
      rewrite <- H5 in H6. auto. intros.
      assert(H'' : In x l1).
      rewrite <- H3. simpl. right. auto.
      apply H0 in H''. auto. rewrite <- H5 in H1. auto.
    + assert(H' : In a l2).
      rewrite <- H5. simpl. left. auto.
      apply H1 in H'. simpl. rewrite H'.
      apply IHl with (l2:=l4).
      auto. auto. intros.
      assert(H'' : In x l2).
      rewrite <- H5. simpl. right. auto.
      apply H1 in H''. auto.
Qed.


