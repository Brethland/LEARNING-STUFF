(*
  Exercises for <Software Foundations> V2 CH8.
  Author : Brethland, Early 2020.
*)

Set Warnings "-notation-overridden,-parsing".
Require Import Strings.String.
Require Import Coq.Logic.FunctionalExtensionality. 
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

Lemma context_invariance : ∀Gamma Gamma' t T,
     Gamma ⊢ t ∈ T →
     (∀x, appears_free_in x t → Gamma x = Gamma' x) →
     Gamma' ⊢ t ∈ T.
Proof with eauto.
  intros.
  generalize dependent Gamma'.
  induction H; intros; auto.
  - apply T_Var. rewrite <- H0...
  - apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    unfold update. unfold t_update. destruct (beq_string x0 x1) eqn: Hx0x1...
    rewrite beq_string_false_iff in Hx0x1. auto.
  - apply T_App with T11...
Qed.

Lemma t_update_shadow : ∀(A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros.
  apply functional_extensionality.
  intros. unfold t_update.
  destruct (beq_string x0 x1) eqn:HE.
  - auto.
  - auto.
Qed.

Theorem beq_string_refl : ∀ s, true = beq_string s s. 
Proof. 
  intros s. unfold beq_string. destruct (string_dec s s) as [|Hs]. 
  - reflexivity.   
  - destruct Hs. reflexivity. 
Qed.

Theorem beq_string_true_iff : ∀ x y : string,   beq_string x y = true ↔ x = y. 
Proof. 
  intros x y. 
  unfold beq_string. 
  destruct (string_dec x y) as [|Hs]. 
  - subst. split. auto. auto.
  - split. 
    + intros contra. inversion contra.
    + intros H. destruct Hs. auto.
Qed.

Theorem beq_string_false_iff : ∀ x y : string,   beq_string x y = false   ↔ x ≠ y. 
Proof. 
  intros x y. rewrite <- beq_string_true_iff. 
  rewrite not_true_iff_false. reflexivity. 
Qed.

Lemma substitution_preserves_typing : ∀Gamma x U t v T,
  (x ⊢> U ; Gamma) ⊢ t ∈ T →
  empty ⊢ v ∈ U →
  Gamma ⊢ [x:=v]t ∈ T.
Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  - (* var *)
    rename s into y. destruct (eqb_spec x y) as [Hxy|Hxy].
    + (* x=y *)
      subst. unfold update in H2.
      rewrite t_update_eq in H2.
      inversion H2; subst.
      eapply context_invariance. eassumption.
      apply typable_empty__closed in Ht'. unfold closed in Ht'.
      intros. apply (Ht' x0) in H0. inversion H0.
    + (* x<>y *)
      apply T_Var. unfold update in H2. rewrite t_update_neq in H2...
  - (* abs *)
    rename s into y. rename t into T. apply T_Abs.
    destruct (eqb_spec x y) as [Hxy | Hxy].
    + (* x=y *)
      subst. unfold update in H5. rewrite t_update_shadow in H5. apply H5.
    + (* x<>y *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_spec y z) as [Hyz | Hyz]; subst; trivial.
      rewrite <- beq_string_false_iff in Hxy.
      rewrite Hxy... rewrite <- beq_string_false_iff in *. rewrite Hyz...
Qed.

Theorem preservation : ∀t t' T,
  empty ⊢ t ∈ T →
  t -->> t' →
  empty ⊢ t' ∈ T.
Proof with eauto.
  remember (@empty ty) as Gamma.
  intros t t' T HT. generalize dependent t'.
  induction HT;
       intros t' HE; subst Gamma; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and eauto takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T11...
      inversion HT1...
Qed.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t ∧ ¬value t.
Corollary soundness : ∀t t' T,
  empty ⊢ t ∈ T →
  t -->* t' →
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  - eapply progress in Hhas_type. destruct Hhas_type;auto.
  - eapply IHHmulti;auto. eapply preservation. apply Hhas_type. auto.
Qed.

Theorem unique_types : ∀Gamma e T T',
  Gamma ⊢ e ∈ T →
  Gamma ⊢ e ∈ T' →
  T = T'.
Proof.
  intros Gamma e. generalize dependent Gamma. 
  induction e;intros;inversion H;subst;inversion H0;subst;auto.
  - rewrite H3 in H4. inversion H4;auto.
  - specialize (IHe2 _ _ _ H6 H8);subst. specialize (IHe1 _ _ _ H4 H5). inversion IHe1. auto.
  - specialize (IHe _ _ _ H6 H7);subst;auto.
  - specialize (IHe2 _ _ _ H7 H10);auto. 
Qed.

Module STLCArith.
Import STLC.

Inductive ty : Type :=
  | Arrow : ty → ty → ty
  | Nat : ty.

Inductive tm : Type :=
  | var : string → tm
  | app : tm → tm → tm
  | abs : string → ty → tm → tm
  | const : nat → tm
  | scc : tm → tm
  | prd : tm → tm
  | mlt : tm → tm → tm
  | test0 : tm → tm → tm → tm.

(* Leaving STLCArith *)