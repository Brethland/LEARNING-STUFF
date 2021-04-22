Require Import Coq.Logic.FunctionalExtensionality.

Definition em := forall A: Prop, A \/ ~ A.
Definition or_dist := forall A B C: Prop, (A -> B \/ C) -> (A -> B) \/ (A -> C).

Lemma em_implies_or_dist: em -> or_dist.
unfold em. unfold or_dist.
intros.
specialize H with A.
destruct H.
- apply H0 in H. destruct H.
  + left. intros. auto.
  + right. intros. auto.
- unfold not in *.
  left. intros. apply H in H1. inversion H1.
Qed.

Lemma silly: forall A: Prop, A -> A \/ A.
intros. auto.
Qed.