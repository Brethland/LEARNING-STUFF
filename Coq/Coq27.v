From Coq Require Import List.

Inductive suf {X : Type} : list X -> list X -> Prop :=
  | SInit (l : list X) : suf l l
  | SCons (x : X) (l l' : list X) (H : suf l l') : suf (x :: l) l'.

Require Import Omega.
Require Import Arith.

Theorem invert : forall a b : nat, a + a = b + b -> a = b.
Proof.
  intros. omega. Qed.
