Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.
Add LoadPath "C:\Users\ycy12\Documents\Workspace\LEARNING-STUFF\Coq".
Load Coq19.

Inductive tm : Type :=
  | C : nat → tm
  | P : tm → tm → tm.

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P a1 a2 => evalF a1 + evalF a2
  end.

Reserved Notation " t '===>' n " (at level 50, left associativity).
Inductive eval : tm → nat → Prop :=
  | E_Const : ∀n,
      C n ===> n
  | E_Plus : ∀t1 t2 n1 n2,
      t1 ===> n1 →
      t2 ===> n2 →
      P t1 t2 ===> (n1 + n2)
where " t '===>' n " := (eval t n).
Module SimpleArith1.

Reserved Notation " t '--->' t' " (at level 40).
Inductive step : tm → tm → Prop :=
  | ST_PlusConstConst : ∀n1 n2,
      P (C n1) (C n2) ---> C (n1 + n2)
  | ST_Plus1 : ∀t1 t1' t2,
      t1 ---> t1' →
      P t1 t2 ---> P t1' t2
  | ST_Plus2 : ∀n1 t2 t2',
      t2 ---> t2' →
      P (C n1) t2 ---> P (C n1) t2'

  where " t '--->' t' " := (step t t').

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
      --->
      P
        (C 0)
        (P
          (C 2)
          (C (0 + 3))).
Proof.
  repeat econstructor.
Qed.
End SimpleArith1.
Definition deterministic {X : Type} (R : relation X) :=
  ∀x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

Module SimpleArith2.
Import SimpleArith1.
Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - (* ST_PlusConstConst *) inversion Hy2.
    + (* ST_PlusConstConst *) reflexivity.
    + (* ST_Plus1 *) inversion H2.
    + (* ST_Plus2 *) inversion H2.
  - (* ST_Plus1 *) inversion Hy2.
    + (* ST_PlusConstConst *)
      rewrite <- H0 in Hy1. inversion Hy1.
    + (* ST_Plus1 *)
      rewrite <- (IHHy1 t1'0).
      reflexivity. assumption.
    + (* ST_Plus2 *)
      rewrite <- H in Hy1. inversion Hy1.
  - (* ST_Plus2 *) inversion Hy2.
    + (* ST_PlusConstConst *)
      rewrite <- H1 in Hy1. inversion Hy1.
    + (* ST_Plus1 *) inversion H2.
    + (* ST_Plus2 *)
      rewrite <- (IHHy1 t2'0).
      reflexivity. assumption.
Qed.

End SimpleArith2.

Inductive value : tm → Prop :=
  | v_const : ∀n, value (C n).

Reserved Notation " t '--->' t' " (at level 40).
Inductive step : tm → tm → Prop :=
  | ST_PlusConstConst : ∀n1 n2,
          P (C n1) (C n2)
      ---> C (n1 + n2)
  | ST_Plus1 : ∀t1 t1' t2,
        t1 ---> t1' →
        P t1 t2 ---> P t1' t2
  | ST_Plus2 : ∀v1 t2 t2',
        value v1 → (* <--- n.b. *)
        t2 ---> t2' →
        P v1 t2 ---> P v1 t2'

  where " t '--->' t' " := (step t t').

Theorem step_deterministic :
  deterministic step.
Proof.
  unfold deterministic. intros.
  generalize dependent y2. induction H; intros.
  - inversion H0;subst.
    + auto.
    + inversion H3.
    + inversion H4.
  - inversion H0.
    + subst. inversion H.
    + rewrite <- (IHstep t1'0). auto. auto.
    + rewrite <- H1 in H. subst. inversion H3;subst.
      inversion H;subst.
  - inversion H0.
    + subst. inversion H1;subst. inversion H;subst.
      inversion H5. inversion H6;subst. auto. inversion H7. inversion H8.
    + subst. inversion H;subst. inversion H1;subst. inversion H6. inversion H1;subst. inversion H4.
      rewrite (IHstep t2'). auto. auto.
    + subst. inversion H;subst. inversion H2;subst.
      inversion H1;subst. inversion H7. rewrite (IHstep t2'). auto. auto.
Qed.

Theorem strong_progress : ∀t,
  value t ∨ (∃t', t ---> t').
Proof.
  induction t.
  - left. constructor.
  - right. destruct IHt1.
    + destruct IHt2.
      inversion H;inversion H0;subst. exists (C (n + n0)). constructor.
      destruct H0. inversion H;subst. exists (P (C n) x). econstructor. auto. auto.
    + destruct H. destruct IHt2.
      inversion H0;subst. exists (P x (C n)). econstructor. auto.
      destruct H0. exists (P x t2). apply ST_Plus1. auto.
Qed.

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ¬∃t', R t t'.

Lemma value_is_nf : ∀v,
  value v → normal_form step v.
Proof.
  unfold normal_form. intros v H. inversion H.
  intros contra. inversion contra. inversion H1.
Qed.

Lemma nf_is_value : ∀t,
  normal_form step t → value t.
Proof. (* a corollary of strong_progress... *)
  unfold normal_form. intros t H.
  assert (G : value t ∨ ∃t', t ---> t').
  { apply strong_progress. }
  destruct G as [G | G].
  - (* l *) apply G.
  - (* r *) exfalso. apply H. assumption.
Qed.

Corollary nf_same_as_value : ∀t,
  normal_form step t ↔ value t.
Proof.
  split. apply nf_is_value. apply value_is_nf.
Qed.

Module Temp4.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm → tm → tm → tm.
Inductive value : tm → Prop :=
  | v_tru : value tru
  | v_fls : value fls.
Reserved Notation " t '--->' t' " (at level 40).
Inductive step : tm → tm → Prop :=
  | ST_IfTrue : ∀t1 t2,
      test tru t1 t2 ---> t1
  | ST_IfFalse : ∀t1 t2,
      test fls t1 t2 ---> t2
  | ST_If : ∀t1 t1' t2 t3,
      t1 ---> t1' →
      test t1 t2 t3 ---> test t1' t2 t3

  where " t '--->' t' " := (step t t').

Theorem strong_progress : ∀t,
  value t ∨ (∃t', t ---> t').
Proof.
  induction t.
  - left. constructor.
  - left. constructor.
  - right. destruct IHt1.
    + inversion H;subst. exists t2. constructor. exists t3. constructor.
    + destruct H. exists (test x t2 t3). econstructor. auto.
Qed.

Theorem step_deterministic :
  deterministic step.
Proof.
  unfold deterministic. intros. generalize dependent y2.
  induction H;intros.
  - inversion H0;subst. auto. inversion H4.
  - inversion H0;subst. auto. inversion H4.
  - inversion H0;subst. inversion H. inversion H.
    rewrite (IHstep t1'0). auto. auto.
Qed.

Module Temp5.

Reserved Notation " t '--->' t' " (at level 40).
Inductive step : tm → tm → Prop :=
  | ST_IfTrue : ∀t1 t2,
      test tru t1 t2 ---> t1
  | ST_IfFalse : ∀t1 t2,
      test fls t1 t2 ---> t2
  | ST_If : ∀t1 t1' t2 t3,
      t1 ---> t1' →
      test t1 t2 t3 ---> test t1' t2 t3
  | ST_Sc : forall t1 t2 t3,
      t2 = t3 ->
      test t1 t2 t3 ---> t2

  where " t '--->' t' " := (step t t').

Definition bool_step_prop4 :
         test
            (test tru tru tru)
            fls
            fls
     --->
         fls.
Proof. apply ST_Sc. auto. Qed.

Theorem strong_progress : ∀t,
  value t ∨ (∃t', t ---> t').
Proof.
  induction t.
  - left. constructor.
  - left. constructor.
  - right. destruct IHt1 as [H | [t' H]].
    + inversion H;subst. exists t2. constructor. exists t3. constructor.
    + exists (test t' t2 t3). econstructor. auto.
Qed.

End Temp5.
End Temp4.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : ∀(x : X), multi R x x
  | multi_step : ∀(x y z : X),
                    R x y →
                    multi R y z →
                    multi R x z.

Notation " t '-->*' t' " := (multi step t t') (at level 40).

Theorem multi_R : ∀(X : Type) (R : relation X) (x y : X),
    R x y → (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.
Qed.

Theorem multi_trans :
  ∀(X : Type) (R : relation X) (x y z : X),
      multi R x y →
      multi R y z →
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption.
Qed.

Lemma test_multistep_2:
  C 3 -->* C 3.
Proof.
  constructor.
Qed.

Lemma test_multistep_3:
      P (C 0) (C 3)
   -->*
      P (C 0) (C 3).
Proof.
  constructor.
Qed.

Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  -->*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  eapply multi_step. apply ST_Plus2. constructor.
  apply ST_Plus2. constructor. apply ST_PlusConstConst.
  eapply multi_step. apply ST_Plus2. constructor.
  apply ST_PlusConstConst. apply multi_refl.
Qed.

Definition step_normal_form := normal_form step.
Definition normal_form_of (t t' : tm) :=
  (t -->* t' ∧ step_normal_form t').

Definition normalizing {X : Type} (R : relation X) :=
  ∀t, ∃t',
    (multi R) t t' ∧ normal_form R t'.

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  unfold deterministic. unfold normal_form_of.
  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1.
  inversion P2 as [P21 P22]; clear P2.
  generalize dependent y2.
  induction P11;intros y2 P21 P22.
  - inversion P21;subst.
    + auto.
    + unfold step_normal_form in *. unfold normal_form in *.
      unfold not in P12. destruct P12. exists y. auto.
  - inversion P21;subst.
    + unfold step_normal_form in *. unfold normal_form in *.
      destruct P22. exists y. auto.
    + assert (H' : y = y0). eapply step_deterministic.
      apply H. apply H0. subst. apply (IHP11 P12 y2) in H1.
      auto. auto.
Qed.