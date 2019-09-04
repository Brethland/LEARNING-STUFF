(*
  A introduction to Coq.
*)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d: day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Inductive nat : Type :=
  | O
  | S (n : nat).

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity).

Compute ((S (S O)) + (S O)).

Theorem plus_O_n : forall n : nat, O + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Lemma plus_comm_z : forall b : nat, O + b = b + O.
Proof.
    intros.
    induction b.
    reflexivity.
    simpl.
    rewrite <- IHb.
    simpl.
    reflexivity.
Qed.

Lemma plus_comm_s : forall a b : nat, S (b + a) = b + S a.
Proof.
    intros.
    induction b.
    simpl.
    reflexivity.
    simpl.
    rewrite IHb.
    reflexivity.
Qed.

Theorem plus_comm : forall a b : nat, a + b = b + a.
Proof.
    intros.
    induction a.
    apply plus_comm_z.
    simpl.
    rewrite IHa.
    apply plus_comm_s.
Qed.