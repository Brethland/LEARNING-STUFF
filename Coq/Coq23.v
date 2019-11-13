Module Coq23.

  Inductive strange : Set :=
    cs : strange -> strange.

  Lemma silly : forall x : strange, cs x = x.
Proof.
  intros.
  induction x. rewrite IHx. auto.
Qed.
  Lemma strange_equ : forall x y : strange, x = y.
 Proof.
    intros. induction x.
    destruct y.
    rewrite <- IHx. apply silly.
Qed.

 Inductive A : Prop :=
   base : Set -> A
 | succ' : A -> A.

 Require Import Nat.
 Require Import Arith.

 Check (succ' (base nat)).
 
