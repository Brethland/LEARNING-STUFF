From Coq Require Import Unicode.Utf8.

Definition peirce := ∀ P Q: Prop,
  ((P → Q) → P) → P.

Definition dne := ∀ P : Prop,
  ~~P → P.

Theorem to : peirce -> dne.
Proof.
  intro.
  unfold peirce in H.
  unfold dne.
  unfold not.
  intro P.
  exfalso.
Qed.
