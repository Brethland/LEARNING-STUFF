(*
  Some Exercise from Software Foundations Book1 CH1.
  Author : Brethland.
*)

Inductive bool : Type :=
  | true
  | false.

Definition andb(b1:bool) (b2:bool) :bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition negb(b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition nandb(b1:bool) (b2:bool) :bool :=
  match b1 with
  | true => (negb b2)
  | false => true
  end.

Example test_nandb1: (nandb true false) = true.
  Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
  Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
  Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
  Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) :bool :=
  match b1 with
  | true => (andb b2 b3)
  | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
  Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
  Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
  Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
  Proof. simpl. reflexivity. Qed.

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits(b1 b2 b3 b4 : bit).

Definition bitzero(a: nybble) :bool :=
  match a with
  | bits(B0 B0 B0 B0) => true
  | bits(_  _  _  _ ) => false
  end.