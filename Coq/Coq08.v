From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.

Lemma silly_eq : forall (n m : nat),
  (S n =? S m) = (n =? m).
Proof.
  intros.
  trivial.
Qed.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intro.
  induction n.
  - destruct m.
    + trivial.
    + trivial.
  - destruct m.
    + trivial.
    + rewrite 2 silly_eq.
      trivial.
Qed.

