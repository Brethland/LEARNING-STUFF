Record iso (A B : Set) : Set :=
  bijection {
    A_to_B : A -> B;
    B_to_A : B -> A;
    A_B_A  : forall a : A, B_to_A (A_to_B a) = a;
    B_A_B  : forall b : B, A_to_B (B_to_A b) = b
  }.

Require Import Arith.
Require Import PeanoNat.
Require Import Omega.

Theorem iso_refl : forall A : Set, iso A A.
Proof.
  intros. apply (bijection _ _ (fun x => x) (fun x => x)).
  auto. auto.
Qed.

Theorem iso_sym : forall A B : Set, iso A B -> iso B A.
Proof.
  intros. inversion H.
  apply (bijection B A B_to_A0 A_to_B0).
  auto. auto.
Qed.

Theorem iso_trans : forall A B C : Set, iso A B -> iso B C -> iso A C.
Proof.
  intros. inversion H. inversion H0.
  apply (bijection A C (fun x => A_to_B1 (A_to_B0 x)) (fun x => (B_to_A0 (B_to_A1 x)))).
  intros. specialize (A_B_A1 (A_to_B0 a)). rewrite A_B_A1. auto.
  intros. specialize (B_A_B0 (B_to_A1 b)). rewrite B_A_B0. auto.
Qed.

Theorem bijection_alt : forall (A B : Set) (A2B : A -> B) (B2A : B -> A),
  (forall a, B2A (A2B a) = a) -> (forall b1 b2, B2A b1 = B2A b2 -> b1 = b2) -> iso A B.
Proof.
  intros. assert(H' : forall b : B, A2B (B2A b) = b).
  intros. specialize (H0 (A2B (B2A b)) b). specialize (H (B2A b)).
  apply H0 in H. auto.
  apply (bijection _ _ A2B B2A H H').
Qed.

Inductive nat_plus_1 : Set := null | is_nat (n : nat).

Definition nat_to_nat_plus_1 (n : nat) : nat_plus_1 :=
  match n with
  | 0 => null
  | S n => is_nat n
  end.

Definition nat_plus_1_to_nat (n : nat_plus_1) : nat :=
  match n with
  | null => 0
  | is_nat n => S n
  end.

Theorem nat_iso_natp1 : iso nat nat_plus_1.
Proof.
  apply (bijection _ _ nat_to_nat_plus_1 nat_plus_1_to_nat).
  intros. destruct a. auto. auto.
  intros. destruct b. auto. auto.
Qed.

Inductive nat_plus_nat : Set := left (n : nat) | right (n : nat).

Fixpoint nat_to_nat_plus_nat (n : nat) :=
  match n with
  | O => left O
  | S n => match nat_to_nat_plus_nat n with
           | left n => right n
           | right n => left (S n)
           end
  end.

Definition nat_plus_nat_to_nat (a : nat_plus_nat) : nat :=
  match a with
  | left n' => n' * 2
  | right n' => S (n' * 2)
  end.

Theorem nat_iso_natpnat : iso nat nat_plus_nat.
Proof.
  apply (bijection _ _ nat_to_nat_plus_nat nat_plus_nat_to_nat);intros.
  - induction a;simpl;auto;destruct (nat_to_nat_plus_nat);subst;simpl;omega.
  - destruct b;simpl;induction n;auto;simpl in *;rewrite IHn;auto.
Qed.