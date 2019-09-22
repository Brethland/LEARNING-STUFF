(*
  Exercises for <Software Foundations> CH6.
  Author : Brethland, Late 2019.
*)

From Coq Require Import Peano.
From Coq Require Import Nat.
From Coq Require Import Arith.
From Coq Require Import List.

Lemma and_intro : forall (A B : Prop),
  A -> B -> and A B.
Proof.
  intros.
  split.
  apply H.
  apply H0.
Qed.

Example and_exercise : forall (n m : nat),
  n + m = 0 -> and (n = 0) (m = 0).
Proof.
  intros.
  apply and_intro.
  - induction n.
    + auto.
    + inversion H.
  - induction m.
    + auto.
    + rewrite plus_comm in H.
      inversion H.
Qed.

Lemma proj1 : forall (P Q : Prop),
  P /\ Q -> P.
Proof.
  intros.
  destruct H.
  auto.
Qed.

Lemma proj2 : forall (P Q : Prop),
  P /\ Q -> Q.
Proof.
  intros.
  destruct H.
  auto.
Qed.

Lemma and_commut : forall (P Q : Prop),
  P /\ Q -> Q /\ P.
Proof.
  intros.
  destruct H.
  split.
  auto.
  auto.
Qed.

Lemma and_assoc : forall (P Q R : Prop),
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  split.
  trivial. trivial. trivial.
Qed.

(* ex falso quodlibet *)

Fact not_implies_our_not : forall (P : Prop),
  ~ P -> (forall (Q :Prop), P -> Q).
Proof.
  intros.
  destruct H.
  auto.
Qed.

Theorem not_False :   ~ False. 
Proof.   
  unfold not. 
  intros H. 
  destruct H. 
Qed.

Lemma contradiction_implies_everything : forall (P Q : Prop),
  (P /\ ~ P) -> Q.
Proof.
  intros P Q [HA HNA].
  unfold not in HNA.
  apply HNA in HA.
  inversion HA.
Qed.

Lemma double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros.
  unfold not.
  intros.
  apply H0.
  auto.
Qed.

Lemma contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~ Q -> ~ P).
Proof.
  intros P Q H.
  unfold not.
  intros.
  apply H in H1.
  apply H0 in H1.
  inversion H1.
Qed.

Fact not_both_true_false : forall P : Prop,
  ~ (P /\ ~ P).
Proof.
  intros.
  unfold not.
  intros [HA HNA].
  apply HNA in HA.
  inversion HA.
Qed.

Theorem not_true_is_false : forall b : bool,   
  b <> true -> b = false. 
Proof. 
  intros [] H.
  - unfold not in H.
    exfalso.
    apply H.
    auto.
  - auto.
Qed.

Lemma True_is_true : True.
Proof.
  apply I.
Qed.

Lemma iff_sym : forall (P Q : Prop),
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  auto.
  auto.
Qed.

Lemma not_true_iff_false : forall b : bool,
  b <> true <-> b = false.
Proof.
  intros b.
  split.
  apply not_true_is_false.
  intros.
  rewrite H.
  intros H'.
  inversion H'.
Qed.

Lemma or_distriutes_over_and : forall (P Q R : Prop),
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [HR | [HQ HR]].
    + auto.
    + auto.
  - intros [[HP | HQ] [HP' | HR]].
    + auto.
    + auto.
    + auto.
    + auto.
Qed.

Require Import Coq.Setoids.Setoid.

Lemma mult_0 : forall (n m : nat),
  n * m = 0 <-> n = 0 \/ m = 0.
Admitted.

Lemma mult_0_3 : forall (n m p : nat),
  n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros.
  rewrite 2 mult_0.
  rewrite or_assoc.
  reflexivity.
Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2.
  auto.
Qed.

Lemma exists_example : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  auto.
Qed.

Lemma dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros.
  unfold not.
  intros.
  destruct H0 as [x E].
  apply E in H.
  inversion H.
Qed.

Lemma dist_exists_or : forall (X : Prop) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split.
  - intros [x0 [HP | HQ]].
    left. exists x0. auto.
    right. exists x0. auto.
  - intros [[x1 E1] | [x2 E2]].
    exists x1. left. auto.
    exists x2. right. auto.
Qed.

Fixpoint In {X : Type} (x : X) (l : list X) :=
  match l with
  | nil => False
  | cons e es => x = e \/ In x es
  end.

Notation "x :: y" := (cons x y)
                    (at level 60, right associativity).
Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                    (at level 60, right associativity).

Example In_example :  forall n, In n [2;4] -> exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. auto.
  - exists 2. auto.
Qed.

