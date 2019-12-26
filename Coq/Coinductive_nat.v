CoInductive conat : Set :=
  | O : conat
  | S : conat -> conat.

CoInductive bisim : conat -> conat -> Prop :=
  | OO : bisim O O
  | SS : forall n m, bisim n m -> bisim (S n) (S m).

Notation "x == y" := (bisim x y) (at level 80) : conat_scope.

CoFixpoint plus (n m : conat) : conat := match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Notation "x + y" := (plus x y) (at level 50, left associativity) : conat_scope.

Require Import Coq.Setoids.Setoid.

Open Scope conat_scope.

Definition conat_u (n : conat) : conat := match n with
  | O => O
  | S n' => S n' end.

Lemma conat_unfold : forall n : conat, n = conat_u n.
Proof. destruct n; auto. Qed.

Lemma bisim_refl : forall m, m == m.
Proof. cofix CIH.
  intros. destruct m;constructor. apply CIH.
Qed.

Lemma bisim_sym : forall m n, m == n -> n == m.
Proof. cofix CIH.
  intros. inversion H;subst;constructor. apply CIH. auto.
Qed.

Lemma bisim_trans : forall m n p, m == n -> n == p -> m == p.
Proof. cofix CIH.
  intros. destruct H. auto. inversion H0;subst.
  constructor. apply CIH with m. auto. auto.
Qed.

Add Parametric Relation: conat bisim
  reflexivity proved by bisim_refl
  symmetry proved by bisim_sym
  transitivity proved by bisim_trans as bisim_rel.

Lemma plus_identity_l n : O + n = n.
Proof. rewrite (conat_unfold n) at 2. 
  apply (conat_unfold (O + n)).
Qed.

Lemma plus_identity_r : forall n, n + O == n.
Proof. cofix CIH.
  intros. destruct n. rewrite plus_identity_l. reflexivity.
  rewrite (conat_unfold (S n + O)). constructor. apply CIH.
Qed.

Lemma plus_Sn_m n m : S n + m = S (n + m).
Proof. apply conat_unfold.
Qed.

Lemma plus_n_Sm : forall n m, n + S m == S (n + m).
Proof. cofix CIH.
  destruct n;intros. do 2 rewrite plus_identity_l;reflexivity.
  rewrite plus_Sn_m. constructor. rewrite plus_Sn_m. apply CIH.
Qed.

Lemma plus_comm_helper : forall n m s t, s == n + m -> t == m + n -> s == t.
Proof. cofix CIH.
  destruct n;intros.
  transitivity (O + m). apply H. symmetry. rewrite plus_identity_l. 
  rewrite plus_identity_r in H0. auto.
  rewrite plus_Sn_m in *. rewrite plus_n_Sm in *. destruct s, t;inversion H;inversion H0.
  constructor. apply CIH with n m. auto. auto.
Qed.

Theorem plus_comm : forall n m, n + m == m + n.
Proof. intros. apply plus_comm_helper with n m;reflexivity. Qed.

Lemma plus_assoc_helper : forall n m p s t, s == (n + m) + p -> t == n + (m + p) -> s == t.
Proof. cofix CIH.
  intros;destruct n.
  transitivity (O + m + p). auto. rewrite plus_identity_l in *. symmetry. auto.
  rewrite plus_Sn_m in *. rewrite plus_Sn_m in H. destruct s, t;inversion H;inversion H0.
  constructor. apply CIH with n m p. auto. auto.
Qed.

Theorem plus_assoc : forall n m p, (n + m) + p == n + (m + p).
Proof. intros. apply plus_assoc_helper with n m p;reflexivity. Qed.