Require Import Arith.
Import Nat.

Definition EM := forall A : Prop, A \/ ~ A.

Definition LPO := forall (f : nat -> bool),
  (forall n : nat, f n = false) \/ (exists n : nat, f n = true).

Definition LLPO := forall (f : nat -> bool),
  (forall n m : nat, n <> m -> f n = false \/ f m = false) ->
    (forall n : nat, even n = true  -> f n = false) \/
    (forall n : nat, even n = false -> f n = false).

Theorem EM_impl_LPO : EM -> LPO.
Proof. unfold EM. unfold LPO.
  intros. destruct H with (exists n : nat, f n = true).
  right. auto.
  left. intros. destruct H with (f n = false).
  auto. destruct H0. exists n. destruct (f n). auto. 
  exfalso. apply H1. auto.
Qed.

Theorem LPO_impl_LLPO : LPO -> LLPO.
Proof.
  unfold LPO. unfold LLPO.
  intros. specialize (H f).
  destruct H. left. auto.
  destruct H. 
  assert (Hev: even x = false \/ even x = true). { destruct (even x); eauto. }
  destruct Hev. left. intros. destruct (Nat.eq_dec x n) eqn:Heq.
  - subst. rewrite H2 in H1. inversion H1.
  - clear Heq. apply H0 in n0. destruct n0. rewrite H3 in H. inversion H. auto.
  - right. intros. destruct (Nat.eq_dec x n) eqn:Heq.
    + subst. rewrite H2 in H1. inversion H1.
    + clear Heq. apply H0 in n0. destruct n0. rewrite H3 in H. inversion H. auto.
Qed.