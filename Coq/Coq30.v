(*
  Exercies for <Software Foundations> V2 CH6.
  Author : Brethland, Late 2019.
*)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
Add LoadPath "C:\Users\ycy12\Documents\Workspace\LEARNING-STUFF\Coq".
Load Coq29.
Hint Constructors multi.

Module Types.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm → tm → tm → tm
  | zro : tm
  | scc : tm → tm
  | prd : tm → tm
  | iszro : tm → tm.

Inductive bvalue : tm → Prop :=
  | bv_tru : bvalue tru
  | bv_fls : bvalue fls.
Inductive nvalue : tm → Prop :=
  | nv_zro : nvalue zro
  | nv_scc : ∀t, nvalue t → nvalue (scc t).
Definition value (t : tm) := bvalue t ∨ nvalue t.
Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold t_update.

Reserved Notation "t1 '--->' t2" (at level 40).
Inductive step : tm → tm → Prop :=
  | ST_TestTru : ∀t1 t2,
      (test tru t1 t2) ---> t1
  | ST_TestFls : ∀t1 t2,
      (test fls t1 t2) ---> t2
  | ST_Test : ∀t1 t1' t2 t3,
      t1 ---> t1' →
      (test t1 t2 t3) ---> (test t1' t2 t3)
  | ST_Scc : ∀t1 t1',
      t1 ---> t1' →
      (scc t1) ---> (scc t1')
  | ST_PrdZro :
      (prd zro) ---> zro
  | ST_PrdScc : ∀t1,
      nvalue t1 →
      (prd (scc t1)) ---> t1
  | ST_Prd : ∀t1 t1',
      t1 ---> t1' →
      (prd t1) ---> (prd t1')
  | ST_IszroZro :
      (iszro zro) ---> tru
  | ST_IszroScc : ∀t1,
       nvalue t1 →
      (iszro (scc t1)) ---> fls
  | ST_Iszro : ∀t1 t1',
      t1 ---> t1' →
      (iszro t1) ---> (iszro t1')

where "t1 '--->' t2" := (step t1 t2).
Hint Constructors step.

Notation step_normal_form := (normal_form step).
Definition stuck (t : tm) : Prop :=
  step_normal_form t ∧ ¬value t.
Hint Unfold stuck.

Example some_term_is_stuck :
  ∃t, stuck t.
Proof.
  exists (scc fls).
  unfold stuck. split. unfold step_normal_form.
  intros [t' H]. inversion H;subst. inversion H1.
  unfold value. intros contra. destruct contra;inversion H;inversion H1.
Qed.

Lemma value_is_nf : ∀t,
  value t → step_normal_form t.
Proof.
  intros. destruct H;induction H;try (intros [t' H1];inversion H1).
  apply IHnvalue. exists t1'. auto.
Qed.

Ltac not_nf x := assert (H' : value x);unfold value;right;auto;apply value_is_nf in H';destruct H';eauto.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  1 - 2 : inversion Hy2;subst;try reflexivity;inversion H3.
  inversion Hy2;subst. 1 - 2 : inversion Hy1. apply (IHHy1 t1'0) in H3;subst;auto.
  inversion Hy2;subst. apply (IHHy1 t1'0) in H0;subst;auto.
  inversion Hy2;auto. inversion H0.
  inversion Hy2;subst;auto. inversion H1;subst. assert (value t1).
  unfold value. right. auto. apply value_is_nf in H0. destruct H0.
  eauto. inversion Hy2;subst. inversion Hy1. inversion Hy1;subst.
  assert (value y2).
  unfold value. right. auto. apply value_is_nf in H. destruct H.
  eauto. apply (IHHy1 t1'0) in H0;subst;auto.
  1 - 2 : inversion Hy2;auto;subst;try inversion H0.
  inversion H1;subst. assert (value t1).
  unfold value. right. auto. apply value_is_nf in H0. destruct H0.
  eauto. inversion Hy2;subst. inversion Hy1. inversion Hy1. subst.
  assert (value t0).
  unfold value. right. auto. apply value_is_nf in H. destruct H.
  eauto. apply (IHHy1 t1'0) in H0;subst;auto.
Qed.

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

Reserved Notation "'⊢' t '∈' T" (at level 40).
Inductive has_type : tm → ty → Prop :=
  | T_Tru :
       ⊢ tru ∈ Bool
  | T_Fls :
       ⊢ fls ∈ Bool
  | T_Test : ∀t1 t2 t3 T,
       ⊢ t1 ∈ Bool →
       ⊢ t2 ∈ T →
       ⊢ t3 ∈ T →
       ⊢ test t1 t2 t3 ∈ T
  | T_Zro :
       ⊢ zro ∈ Nat
  | T_Scc : ∀t1,
       ⊢ t1 ∈ Nat →
       ⊢ scc t1 ∈ Nat
  | T_Prd : ∀t1,
       ⊢ t1 ∈ Nat →
       ⊢ prd t1 ∈ Nat
  | T_Iszro : ∀t1,
       ⊢ t1 ∈ Nat →
       ⊢ iszro t1 ∈ Bool

where "'⊢' t '∈' T" := (has_type t T).
Hint Constructors has_type.

Example scc_hastype_nat__hastype_nat : ∀t,
  ⊢ scc t ∈ Nat →
  ⊢ t ∈ Nat.
Proof. inversion 1;auto.
Qed.

Lemma bool_canonical : ∀t,
  ⊢ t ∈ Bool → value t → bvalue t.
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - induction Hn; inversion HT; auto.
Qed.

Lemma nat_canonical : ∀t,
  ⊢ t ∈ Nat → value t → nvalue t.
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.

Theorem progress : ∀t T,
  ⊢ t ∈ T →
  value t ∨ ∃t', t ---> t'.
Proof with auto.
  intros t T HT.
  induction HT...
  - right. inversion IHHT1; clear IHHT1.
    + apply (bool_canonical t1 HT1) in H.
      inversion H; subst; clear H.
      exists t2...
      exists t3...
    + inversion H as [t1' H1].
      exists (test t1' t2 t3)...
  - inversion IHHT; clear IHHT.
    + apply (nat_canonical t1 HT) in H. left.
      inversion H; subst; clear H...
    + inversion H. right. exists (scc x)...
  - inversion IHHT; clear IHHT.
    + apply (nat_canonical t1 HT) in H. right. 
      inversion H;subst.
      exists zro... exists t...
    + inversion H. right. exists (prd x)...
  - inversion IHHT; clear IHHT.
    + apply (nat_canonical t1 HT) in H. right.
      inversion H;subst. exists tru... exists fls...
    + inversion H. right. exists (iszro x)...
Qed.

Theorem preservation : ∀t t' T,
  ⊢ t ∈ T →
  t ---> t' →
  ⊢ t' ∈ T.
Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         intros t' HE.
  1 - 2 : inversion HE.
  inversion HE; subst; clear HE;try assumption.
  econstructor; try assumption.
      apply IHHT1...
  1 - 3 : inversion HE;subst. inversion HE;subst. econstructor;apply IHHT...
  auto. eapply scc_hastype_nat__hastype_nat. auto. econstructor...
  inversion HE;subst;econstructor. apply IHHT...
Qed.

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
Corollary soundness : ∀t t' T,
  ⊢ t ∈ T →
  t -->* t' →
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.
  apply IHP. apply (preservation x y T HT H).
  unfold stuck. split; auto. Qed.