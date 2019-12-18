(*
  Exercises for <Software Foundations> V2 CH3.
  Arthur : Brethland, Late 2019.
 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Strings.String.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
Add LoadPath "C:\Users\ycy12\Documents\Workspace\LEARNING-STUFF\Coq".
Load Coq24.

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

Lemma parity_ge_2 : ∀x,
  2 ≤ x →
  parity (x - 2) = parity x.
Proof.
  induction x; intro. reflexivity.
  destruct x. inversion H. inversion H1.
  simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Lemma parity_lt_2 : ∀x,
  ¬2 ≤ x →
  parity (x) = x.
Proof.
  intros. induction x. reflexivity. destruct x. reflexivity.
    exfalso. apply H. omega.
Qed.

Lemma silly : forall n m, n <= m -> S n <= S m.
Proof. intros. omega. Qed.

Lemma silly2 : forall n m, S n <= S m -> n <= m.
Proof. intros. omega. Qed.

Theorem le_ble_nat : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on [m]. *)
  intros. generalize dependent n. induction m.
  - intros. inversion H. simpl. reflexivity.
  - intros. destruct n.
    + simpl. reflexivity.
    + simpl. apply IHm. apply silly2. apply H.
Qed.

Theorem ble_nat_true : forall n m,
  n <=? m = true -> n <= m.
Proof. 
  induction n.
  - intros. omega.
  - intros. destruct m.
    + inversion H.
    + simpl in H. apply silly. apply IHn. apply H.
Qed.

Theorem ble_nat_false : forall n m,
  n <=? m = false -> ~(n <= m).
Proof.
  unfold not. intros. apply le_ble_nat in H0. rewrite H0 in H. inversion H.
Qed.

Lemma fuck : forall b, ~(b = true) -> b = false.
Proof. intros. destruct b. exfalso. apply H. auto. auto.
Qed.

Theorem parity_correct : forall m,
    {{ fun st => st X = m }}
  (WHILE 2 ≤ X DO
    X ::= X - 2
  END)
    {{ fun st => st X = parity m }}.
Proof.
  intros. eapply hoare_consequence_post.
  apply hoare_consequence_pre with (fun st => parity (st X) = parity m).
  apply hoare_while. eapply hoare_consequence_pre. apply hoare_asgn.
  unfold assert_implies, assn_sub, t_update.
  intros. simpl. destruct H. rewrite <- H. apply parity_ge_2. apply ble_nat_true. apply H0.
  unfold assert_implies, assn_sub, t_update.
  intros. auto.
  unfold assert_implies, assn_sub, t_update.
  intros. destruct H. rewrite <- H. symmetry. apply parity_lt_2. 
  unfold bassn in H0. apply ble_nat_false. unfold not in H0. apply fuck. auto.
Qed.

Definition is_wp P c Q :=
  {{P}} c {{Q}} ∧
  ∀P', {{P'}} c {{Q}} → (P' ->> P).

Theorem is_wp_example :
  is_wp (fun st => st Y ≤ 4)
    (X ::= Y + 1) (fun st => st X ≤ 5).
Proof.
  unfold is_wp. split.
  - eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. unfold assn_sub, t_update. simpl. omega.
  - intros. intros st H'. unfold hoare_triple in H.
    eapply H in H'. 