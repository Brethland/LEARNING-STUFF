(*
  Exercises for <Software Foundations> CH11.
  Author : Brethland, Late 2019.
*)

Require Import Coq.Arith.Arith. 
Require Import Coq.Bool.Bool. 
Require Export Coq.Strings.String. 
Require Import Coq.Logic.FunctionalExtensionality. 
Require Import Coq.Lists.List.
Require Import Unicode.Utf8.
Require Import Setoid.
Require Import PeanoNat.
Require Import Peano.
Require Import Arith.
Require Import List.
Require Import Omega.

Definition relation (X: Type) := X → X → Prop.

Definition partial_function {X: Type} (R: relation X) :=   ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2. 

Inductive next_nat (n : nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros. inversion H.
  inversion H0.
  auto.
Qed.

Inductive total_relation : nat -> nat -> Prop :=
  | tl : forall n m, (le n m) \/ (le m n) -> total_relation n m.
Inductive empty_relation : nat -> nat -> Prop :=
  | el : forall n, next_nat (S n) n -> empty_relation n (S n).

Lemma total_relation_not_partial : ~ (partial_function total_relation).
Proof.
  unfold not. unfold partial_function. intros.
  assert (contra : 0 = 1).
  { apply H with (x :=2).
    apply tl. right. omega.
    apply tl. right. omega.
  } inversion contra.
Qed.

Lemma empty_relation_partial : partial_function empty_relation.
Proof.
  unfold partial_function. intros.
  inversion H. inversion H0. auto.
Qed.

Definition reflexive {X: Type} (R: relation X) :=
  ∀a : X, R a a.

Definition transitive {X: Type} (R: relation X) :=   ∀ a b c : X, (R a b) → (R b c) → (R a c). 

Theorem le_trans :   transitive le. 
Proof.   
  intros n m o Hnm Hmo.   
  induction Hmo.   
  - (* le_n *) apply Hnm.   
  - (* le_S *) apply le_S. apply IHHmo. 
Qed.

Theorem lt_trans:   transitive lt. 
Proof.   
  unfold lt. unfold transitive.   
  intros n m o Hnm Hmo.   
  apply le_S in Hnm.   
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).   
  apply Hnm.   
  apply Hmo. 
Qed.

Theorem lt_trans' :   transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros.
  induction H0.
  - apply le_S. auto.
  - apply le_S. auto.
Qed.

Theorem lt_trans'' :   transitive lt. 
Proof.   
  unfold lt. unfold transitive.   
  intros.  
  induction c.
  - inversion H0.
  - apply le_trans with (a := (S a)) (b := (S b)) (c := (S c)).
    + apply le_S. auto.
    + auto.
Qed.

Theorem le_S_n : ∀ n m,   (S n ≤ S m) → (n ≤ m).
Proof.
  intros.
  inversion H.
  - auto.
  - omega.
Qed.

Theorem le_Sn_n : ∀ n,   ¬ (S n ≤ n).
Proof.
  unfold not.
  intros. induction n.
  - inversion H.
  - apply IHn. 
    apply le_S_n. auto.
Qed.

Definition symmetric {X: Type} (R: relation X) :=   ∀ a b : X, (R a b) → (R b a).

Theorem le_not_symmetric :   ¬ (symmetric le).
Proof.
  unfold not. unfold symmetric.
  intros.
  assert (H' : 1 <= 0).
  { apply H with (a := 0) (b := 1).
    auto.
  } inversion H'.
Qed.

Definition antisymmetric {X: Type} (R: relation X) := ∀ a b : X, (R a b) → (R b a) → a = b.

Lemma le_Sn_m : forall n m, S n <= m -> n <= m.
Proof. intros. omega. Qed.

Theorem le_antisymmetric :   antisymmetric le.
Proof.
  unfold antisymmetric. intros. generalize dependent a.
  induction b.
  - intros. inversion H. auto.
  - intros. destruct a.
    + inversion H0.
    + assert (H' : a = b -> S a = S b).
      intros. rewrite H1. auto.
      apply H'. apply IHb. apply le_S_n in H. 
      auto. apply le_S_n in H0. auto.
Qed.

Theorem le_step : ∀ n m p,   n < m →   m ≤ S p →   n ≤ p. 
Proof.
  unfold lt. intros.
  inversion H0.
  - rewrite H1 in H. apply le_S_n. auto.
  - apply le_Sn_m in H. apply le_trans with (b:=m).
    auto. auto.
Qed.

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=     
  | rt_step : ∀ x y, R x y → clos_refl_trans R x y     
  | rt_refl : ∀ x, clos_refl_trans R x x     
  | rt_trans : ∀ x y z, clos_refl_trans R x y → clos_refl_trans R y z → clos_refl_trans R x z.

Theorem next_nat_closure_is_le : ∀ n m,   (n ≤ m) ↔ ((clos_refl_trans next_nat) n m). 
Proof.
  intros. split.
  - intros. induction H.
    + apply rt_refl.
    + apply rt_trans with m. auto.
      apply rt_step. apply nn.
  - intros. induction H.
    + inversion H. apply le_S, le_n.
    + apply le_n.
    + apply le_trans with y. auto. auto.
Qed.

Inductive clos_refl_trans_1n {A : Type} (R : relation A) (x : A) : A → Prop :=   
  | rt1n_refl : clos_refl_trans_1n R x x   
  | rt1n_trans (y z : A) : R x y → clos_refl_trans_1n R y z → clos_refl_trans_1n R x z.

Lemma rsc_R : ∀(X:Type) (R:relation X) (x y : X),
       R x y → clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl. Qed.

Lemma rsc_trans :
  ∀(X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y →
      clos_refl_trans_1n R y z →
      clos_refl_trans_1n R x z.
Proof.
  intros.
  induction H.
  - auto.
  - apply rt1n_trans with y. auto. apply IHclos_refl_trans_1n. auto.
Qed.

Theorem rtc_rsc_coincide :
         ∀(X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y ↔ clos_refl_trans_1n R x y.
Proof.
  intros. split.
  - intros. induction H.
    + apply rsc_R. auto.
    + apply rt1n_refl.
    + apply rsc_trans with (y:=y). auto. auto.
  - intros. induction H.
    + apply rt_refl.
    + apply rt_trans with y. apply rt_step. auto.
      auto.
Qed.

