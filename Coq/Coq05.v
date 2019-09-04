(*
  Church Number in Coq.
*)

Definition apply3 {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition czero : cnat := fun (X : Type) (_ : X -> X) (x : X) => x.
Definition cone  : cnat := fun (X : Type) (f : X -> X) (x : X) => f x.
Definition ctwo  : cnat := fun _ f x => f (f x).
Definition cthree : cnat := @apply3.
(* Definition cthree       := fun _ f x => f (f (f x)).*)

Definition cadd (c1 c2 : cnat) : cnat := fun _ f x => c1 _ f (c2 _ f x).
Compute (cadd cone ctwo).

Definition cmul (c1 c2 : cnat) : cnat := fun _ f x => c1 _ (c2 _ f) x.
Compute (cmul (cadd cone ctwo) ctwo) _ S O.

Definition cpow (c1 c2 : cnat) : cnat := fun _ f x => (c2 _ (c1 _) f) x.
Compute (cpow ctwo cthree) _ S O.

(*
Definition cadd (c1 c2 : cnat) : cnat := fun f x => (c1 f (c2 f x)).
Compute (cadd cone ctwo) nat S O.
*)