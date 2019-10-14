Require Import Coq.Arith.Arith.
Require Import Omega.
Require Import Unicode.Utf8.

Inductive div : nat -> nat -> Prop :=
  | zero_div : forall n, div 0 n
  | add_div : forall n m, div n m -> div (n + m) m.

Inductive coprime : nat -> nat -> Prop :=
  | div_co : forall n m, div n m -> coprime (n + 1) m
  | pred_co : forall n, coprime (n + 1) n
  | basic : coprime 1 1.

Lemma silly_114514 : forall n, div n 1.
Proof.
  induction n.
  - apply zero_div.
  - assert(H' : S n = n + 1).
    rewrite plus_comm. auto. rewrite H'.
    apply add_div. auto.
Qed.

Lemma coprime_1_n : forall n, coprime (S n) 1.
Proof.
  intros. assert(H' : S n = n + 1).
    rewrite plus_comm. auto. 
    rewrite H'. apply div_co. apply silly_114514.
Qed.

Lemma coprime_ex : forall n m, coprime n m -> coprime m n.
Proof.
  intros.
  inversion H.
  - inversion H0.
    + simpl. destruct m.
  Abort.

Inductive Coprime : nat -> nat -> Prop :=
  | basic_co :                                  Coprime 1 1
  | addL_co  : forall n m, Coprime n m -> Coprime (n + m) m
  | addR_co  : forall n m, Coprime n m -> Coprime n (m + n).

Lemma coprime_ex : forall n m, Coprime n m -> Coprime m n.
Proof.
  intros. induction H;
  try (constructor;auto).
Qed.

Lemma Coprime_not_involutive : forall n, 1 <= n -> ~(Coprime n n).
Proof.
  intros. unfold not in *. induction n.
  - inversion H.
  - intros. 
