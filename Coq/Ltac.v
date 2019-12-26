Require Import ZArith Lia Omega.

Open Scope Z_scope.

Inductive tarai_r : Z -> Z -> Z -> Z -> Prop :=
| tac_le : forall x y z, x <= y -> tarai_r x y z y
| tac_gt : forall x y z u v w m,
    x > y
    -> tarai_r (x - 1) y z u
    -> tarai_r (y - 1) z x v
    -> tarai_r (z - 1) x y w
    -> tarai_r u v w m
    -> tarai_r x y z m.

Ltac dz x y := destruct (Z.leb_spec x y).

Ltac dest_leb := 
  match goal with
  | [ |- context [ ?x <=? ?y ] ] => dz x y
  | [ H : context [ ?x <=? ?y ] |- _ ] => dz x y
  end.

Theorem tarai_r_correct :
  forall x y z w,
  tarai_r x y z w
  -> w = if x <=? y then y
         else if y <=? z then z
         else x.
Proof.
  intros;induction H;repeat (dest_leb;try lia). Qed.