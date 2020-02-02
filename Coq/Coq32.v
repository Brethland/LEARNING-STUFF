(*
  Exercises for <Software Foundations> V2 CH8.
  Author : Brethland, Early 2020.
*)

Set Warnings "-notation-overridden,-parsing".
Require Import Strings.String.
Add LoadPath "C:\Users\ycy12\Documents\Workspace\LEARNING-STUFF\Coq".
Load Coq31.

Module STLCProp.
Import STLC.

Lemma canonical_forms_bool : ∀t,
  empty ⊢ t ∈ Bool →
  value t →
  (t = tru) ∨ (t = fls).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.

Lemma canonical_forms_fun : ∀t T1 T2,
  empty ⊢ t ∈ (Arrow T1 T2) →
  value t →
  exists x u, t = abs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists x0, t0. auto.
Qed.

Theorem progress : ∀t T,
  empty ⊢ t ∈ T →
  value t ∨ ∃t', t -->> t'.
Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  induction Ht; subst Gamma...
  - (* T_Var *)
    (* contradictory: variables cannot be typed in an
       empty context *)
    inversion H.
  - (* T_App *)
    (* t = t1 t2.  Proceed by cases on whether t1 is a
       value or steps... *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is also a value *)
        assert (∃x0 t0, t1 = abs x0 T11 t0).
        eapply canonical_forms_fun; eauto.
        destruct H1 as [x0 [t0 Heq]]. subst.
        exists ([x0:=t2]t0)...
      * (* t2 steps *)
        inversion H0 as [t2' Hstp]. exists (app t1 t2')...
    + (* t1 steps *)
      inversion H as [t1' Hstp]. exists (app t1' t2)...
  - (* T_Test *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct (canonical_forms_bool t1); subst; eauto.
    + (* t1 also steps *)
      inversion H as [t1' Hstp]. exists (test t1' t2 t3)...
Qed.

Theorem progress' : ∀t T,
     empty ⊢ t ∈ T →
     value t ∨ ∃t', t -->> t'.
Proof with eauto.
  intros t.
  induction t; intros T Ht; auto.
  - inversion Ht;subst. inversion H1.
  - inversion Ht;subst. right. destruct (IHt1 (Arrow T11 T))...
    destruct (IHt2 T11)... assert(exists x0 t0, t1 = abs x0 T11 t0). 
    eapply canonical_forms_fun; eauto. destruct H1 as [x0 [t0 H1]];subst.
    exists ([x0:=t2]t0)...
    destruct H0. exists (app t1 x0)... destruct H. exists (app x0 t2)...
  - right. inversion Ht;subst. destruct (IHt1 Bool)... 
    destruct (canonical_forms_bool t1); subst; eauto. destruct H. exists (test x0 t2 t3)...
Qed.

Inductive appears_free_in : string → tm → Prop :=
  | afi_var : ∀x,
      appears_free_in x (var x)
  | afi_app1 : ∀x t1 t2,
      appears_free_in x t1 →
      appears_free_in x (app t1 t2)
  | afi_app2 : ∀x t1 t2,
      appears_free_in x t2 →
      appears_free_in x (app t1 t2)
  | afi_abs : ∀x y T11 t12,
      y ≠ x →
      appears_free_in x t12 →
      appears_free_in x (abs y T11 t12)
  | afi_test1 : ∀x t1 t2 t3,
      appears_free_in x t1 →
      appears_free_in x (test t1 t2 t3)
  | afi_test2 : ∀x t1 t2 t3,
      appears_free_in x t2 →
      appears_free_in x (test t1 t2 t3)
  | afi_test3 : ∀x t1 t2 t3,
      appears_free_in x t3 →
      appears_free_in x (test t1 t2 t3).
Hint Constructors appears_free_in.

Definition closed (t:tm) :=
  ∀x, ¬appears_free_in x t.

Lemma free_in_context : ∀x t T Gamma,
   appears_free_in x t →
   Gamma ⊢ t ∈ T →
   ∃T', Gamma x = Some T'.
Proof.
  intros x t T Gamma H H0. generalize dependent Gamma.
  generalize dependent T.
  induction H;
         intros; try solve [inversion H0; eauto].
  - (* afi_abs *)
    inversion H1; subst.
    apply IHappears_free_in in H7. unfold update in H7.
    rewrite t_update_neq in H7; assumption.
Qed.

Corollary typable_empty__closed : ∀t T,
    empty ⊢ t ∈ T →
    closed t.
Proof.
  intros. inversion H;subst;unfold closed in *.
  1 : inversion H0.
  all : intros x contra.
  1 : apply (free_in_context _ _ (Arrow T11 T12) empty) in contra;auto.
  3 - 4 : apply (free_in_context _ _ Bool empty) in contra;inversion contra;inversion H0;auto.
  2 - 3 : apply (free_in_context _ _ T empty) in contra;auto.
  all : destruct contra as [m H']; inversion H'.
Qed.
