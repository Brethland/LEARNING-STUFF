Require Import Relation_Definitions Setoid Omega.
Inductive mod_equiv : nat -> nat -> nat -> Prop :=
  | mod_intro_same : forall m n, mod_equiv m n n
  | mod_intro_plus_l : forall m n1 n2, mod_equiv m n1 n2 -> mod_equiv m (m + n1) n2
  | mod_intro_plus_r : forall m n1 n2, mod_equiv m n1 n2 -> mod_equiv m n1 (m + n2).

(* Analogous to the mathematical notation `x == y (mod z)` *)
Notation "x == y %% z" := (mod_equiv z x y) (at level 70).

Notation "'x==x'" := mod_intro_same.
Notation "'m+x==y'" := mod_intro_plus_l.
Notation "'x==m+y'" := mod_intro_plus_r.

Lemma silly : forall m n1 n2,  (m + n1) == n2 %% m -> n1 == n2 %% m.
Proof. 
  intros. remember (m + n1) as n'. induction H;subst;try constructor.
  constructor. replace n1 with n0. auto. omega. apply IHmod_equiv. auto.
Qed.

Lemma mod_sym : forall m n1 n2, n1 == n2 %% m -> n2 == n1 %% m.
Proof.
  intros. induction H;simpl;constructor;auto. Qed.

Lemma mod_trans : forall m n1 n2 n3, n1 == n2 %% m -> n2 == n3 %% m -> n1 == n3 %% m.
Proof. 
  intros. induction H. auto. 
  constructor. apply IHmod_equiv. auto.
  apply silly in H0. apply IHmod_equiv. auto.
Qed.

Add Parametric Relation (m:nat) : nat (mod_equiv m)
  reflexivity proved by (mod_intro_same m)
  symmetry proved by (mod_sym m)
  transitivity proved by (mod_trans m) as mod_equiv_rel.

Lemma plus_one_side : forall m n1 n2 n', n1 == n2 %% m -> n' + n1 == n' + n2 %% m.
Proof.
  intros;induction H;try reflexivity;rewrite plus_assoc;rewrite (plus_comm n' m);
  rewrite <- plus_assoc;constructor;auto.
Qed. 

Add Parametric Morphism (m: nat) : plus
  with signature (mod_equiv m) ==> (mod_equiv m) ==> (mod_equiv m) as plus_mor.
Proof.
  intros. induction H;try (apply plus_one_side;auto);
  try rewrite <- plus_assoc;constructor;apply IHmod_equiv;auto.
Qed.

Lemma mult_one_side : forall m n1 n2 n', n1 == n2 %% m -> n' * n1 == n' * n2 %% m.
Proof.
  assert (H' : forall m n1 n2 p, n1 == n2 %% m -> (p * m + n1) == n2 %% m).
  intros;induction p;auto;simpl. rewrite <- plus_assoc. constructor. auto.
  intros;induction H;try reflexivity. rewrite Nat.mul_add_distr_l.
  apply H'. auto. rewrite Nat.mul_add_distr_l. symmetry. apply H'. symmetry. auto.
Qed.

Add Parametric Morphism (m:nat) : mult
  with signature (mod_equiv m) ==> (mod_equiv m) ==> (mod_equiv m) as mult_mor.
Proof.
  assert (H' : forall m n1 n2 p, n1 == n2 %% m -> (p * m + n1) == n2 %% m).
  intros;induction p;auto;simpl. rewrite <- plus_assoc. constructor. auto.
  intros. induction H.
  - apply mult_one_side. auto.
  - rewrite Nat.mul_add_distr_r. rewrite mult_comm. apply H'. apply IHmod_equiv. auto.
  - symmetry. rewrite Nat.mul_add_distr_r. rewrite mult_comm. apply H'. symmetry.
    apply IHmod_equiv. auto.
Qed.