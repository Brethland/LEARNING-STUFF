Section Inductive_types.

  Inductive bool : Type :=
  | tru : bool
  | fla : bool.

  Definition and (m : bool) (n : bool) : bool :=
    match m with
    | tru => n
    | fla => fla
    end.

  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Fixpoint plus (m : nat) (n : nat) : nat :=
    match m with
    | O => n
    | S m' => S (plus m' n)
    end.

  Definition or m n : bool :=
    match m with
    | tru => tru
    | fla => n
    end.

  Lemma and_eq_or : 
  forall m n :bool,
  (and m n = or m n) -> m = n.
  Proof.
    intros m n.
    destruct m.
    - destruct n.
      + reflexivity.
      + simpl. intros H. rewrite -> H. reflexivity. (* inversion H. *)
    - destruct n.
      + simpl. intros H. inversion H.
      + reflexivity.
  Qed.

  Lemma and_eq_or' : forall m n :bool,
      (and m n = or m n) -> m = n.
    intros;now case m, n. Qed.

  Fixpoint mult m n : nat :=
    match m with
    | O => O
    | S m' => plus n (mult m' n)
    end.

  Fixpoint exp m n : nat :=
    match n with
    | O => S O
    | S n' => mult m (exp m n')
    end.

  Lemma Mzeror : forall m, mult m O = O.
    intros;now elim m. Qed.

  Axiom Msymm : forall m n, mult m n = mult n m.
  Axiom mult_dist_plus : forall m n1 n2,
      mult m (plus n1 n2) = plus (mult m n1) (mult m n2).

  Lemma exp_plus_dist_mult : forall m n1 n2,
      exp m (plus n1 n2) = mult (exp m n1) (exp m n2).
  Proof.
    induction n1;intros;simpl.
    - assert(Pidr : forall m, plus m O = m).
      {
        induction m0;simpl.
        - reflexivity.
        - rewrite -> IHm0. reflexivity.
      }
      rewrite (Pidr (exp m n2)). reflexivity.
    - rewrite IHn1.
      assert(Massoc : forall a b c, mult a (mult b c) = mult (mult a b) c).
      {
        induction b;simpl;intros.
        - rewrite Mzeror. reflexivity.
        - rewrite (Msymm a (S b)). simpl.
          rewrite (Msymm b a), (Msymm (plus a (mult a b)) c).
          do 2 rewrite mult_dist_plus. rewrite IHb.
          rewrite (Msymm c a), (Msymm c (mult a b)). reflexivity.
      }
      rewrite Massoc. reflexivity.
  Qed.

  Check nat_ind.
  Check bool_ind.

End Inductive_types.

Require Import Setoid.
Set Implicit Arguments.
  
Section Set_equality.

  Parameter set : Type -> Type.
  Context {A : Type}.
  Parameter eq_set : set A -> set A -> Prop.
  Axiom eq_set_refl  : forall a, eq_set a a.
  Axiom eq_set_sym   : forall a b, eq_set a b -> eq_set b a.
  Axiom eq_set_trans : forall a b c, eq_set a b -> eq_set b c -> eq_set a c.

  Add Parametric Relation : (set A) (eq_set)
      reflexivity  proved by eq_set_refl
      symmetry     proved by eq_set_sym
      transitivity proved by eq_set_trans as eq_set_rel.

End Set_equality.

Section Div_morphsim.

  Let nonzero : nat -> nat -> Prop := fun x y => x = y /\ x <> O.
  Parameter div : nat -> nat -> nat.
  Axiom div_repl : forall y x1 x2, nonzero x1 x2 -> div y x1 = div y x2.

  Add Parametric Morphism :
    div with signature eq ==> nonzero ==> eq as div_mor.
  exact div_repl. Qed.

End Div_morphsim.

