(*
  This is the exercise for <Software Foundations> V2 CH10.
  Author: Brethland, Early 2020.
*)

Require Import Strings.String.
Add LoadPath "C:\Users\ycy12\Documents\Workspace\LEARNING-STUFF\Coq".
Load Coq30.

Inductive tys : Type :=
  | Top : tys
  | Bool' : tys
  | Base : string → tys
  | Arrow' : tys → tys → tys
  | Unit : tys
.
Inductive tms : Type :=
  | var' : string → tms
  | app' : tms → tms → tms
  | abs' : string → tys → tms → tms
  | tru' : tms
  | fls' : tms
  | test' : tms → tms → tms → tms
  | unit : tms
.

Fixpoint subst (x:string) (s:tms) (t:tms) : tms :=
  match t with
  | var' y =>
      if eqb x y then s else t
  | abs' y T t1 =>
      abs' y T (if eqb x y then t1 else (subst x s t1))
  | app' t1 t2 =>
      app' (subst x s t1) (subst x s t2)
  | tru' =>
      tru'
  | fls' =>
      fls'
  | test' t1 t2 t3 =>
      test' (subst x s t1) (subst x s t2) (subst x s t3)
  | unit =>
      unit
  end.
Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Inductive value' : tms → Prop :=
  | v_abs : ∀x T t,
      value' (abs' x T t)
  | v_true :
      value' tru'
  | v_false :
      value' fls'
  | v_unit :
      value' unit
.
Hint Constructors value'.
Reserved Notation "t1 '--->' t2" (at level 40).
Inductive step' : tms → tms → Prop :=
  | ST_AppAbs : ∀x T t12 v2,
         value' v2 →
         (app' (abs' x T t12) v2) ---> [x:=v2]t12
  | ST_App1 : ∀t1 t1' t2,
         t1 ---> t1' →
         (app' t1 t2) ---> (app' t1' t2)
  | ST_App2 : ∀v1 t2 t2',
         value' v1 →
         t2 ---> t2' →
         (app' v1 t2) ---> (app' v1 t2')
  | ST_TestTrue : ∀t1 t2,
      (test' tru' t1 t2) ---> t1
  | ST_TestFalse : ∀t1 t2,
      (test' fls' t1 t2) ---> t2
  | ST_Test' : ∀t1 t1' t2 t3,
      t1 ---> t1' →
      (test' t1 t2 t3) ---> (test' t1' t2 t3)
where "t1 '--->' t2" := (step' t1 t2).
Hint Constructors step'.

Reserved Notation "T '<:' U" (at level 40).
Inductive subtype : tys → tys → Prop :=
  | S_Refl : ∀T,
      T <: T
  | S_Trans : ∀S U T,
      S <: U →
      U <: T →
      S <: T
  | S_Top : ∀S,
      S <: Top
  | S_Arrow : ∀S1 S2 T1 T2,
      T1 <: S1 →
      S2 <: T2 →
      (Arrow' S1 S2) <: (Arrow' T1 T2)
where "T '<:' U" := (subtype T U).

Hint Constructors subtype.
Module Examples.
Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation z := "z".
Notation A := (Base "A").
Notation B := (Base "B").
Notation C := (Base "C").
Notation String := (Base "String").
Notation Float := (Base "Float").
Notation Integer := (Base "Integer").
Example subtyping_example_0 :
  (Arrow' C Bool') <: (Arrow' C Top).
  (* C->Bool <: C->Top *)
Proof. auto. Qed.

End Examples.

Definition partial_map (A : Type) := total_map (option A).
Definition empty {A : Type} : partial_map A :=
  t_empty None.
Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '⊢>' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).
Notation "x '⊢>' v" := (update empty x v)
  (at level 100).

Definition context := partial_map tys.
Reserved Notation "Gamma '⊢' t '∈' T" (at level 40).
Inductive has_type' : context → tms → tys → Prop :=
  (* Same as before *)
  | T_Var : ∀Gamma x T,
      Gamma x = Some T →
      Gamma ⊢ var' x ∈ T
  | T_Abs : ∀Gamma x T11 T12 t12,
      (x ⊢> T11 ; Gamma) ⊢ t12 ∈ T12 →
      Gamma ⊢ abs' x T11 t12 ∈ Arrow' T11 T12
  | T_App : ∀T1 T2 Gamma t1 t2,
      Gamma ⊢ t1 ∈ Arrow' T1 T2 →
      Gamma ⊢ t2 ∈ T1 →
      Gamma ⊢ app' t1 t2 ∈ T2
  | T_True : ∀Gamma,
       Gamma ⊢ tru' ∈ Bool'
  | T_False : ∀Gamma,
       Gamma ⊢ fls' ∈ Bool'
  | T_Test' : ∀t1 t2 t3 T Gamma,
       Gamma ⊢ t1 ∈ Bool' →
       Gamma ⊢ t2 ∈ T →
       Gamma ⊢ t3 ∈ T →
       Gamma ⊢ test' t1 t2 t3 ∈ T
  | T_Unit : ∀Gamma,
      Gamma ⊢ unit ∈ Unit
  | T_Sub : ∀Gamma t S T,
      Gamma ⊢ t ∈ S →
      S <: T →
      Gamma ⊢ t ∈ T

where "Gamma '⊢' t '∈' T" := (has_type' Gamma t T).
Hint Constructors has_type'.

Hint Extern 2 (has_type' _ (app' _ _) _) =>
  eapply T_App; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.
Module Examples2.
  Import Examples.

End Examples2.

Lemma sub_inversion_Bool : ∀U,
     U <: Bool' →
     U = Bool'.
Proof with auto.
  intros U Hs.
  remember Bool' as V.
  induction Hs;inversion HeqV;auto.
  apply IHHs2 in H;subst. auto.
Qed.

Lemma sub_inversion_arrow : ∀U V1 V2,
     U <: Arrow' V1 V2 →
     ∃U1 U2,
     U = Arrow' U1 U2 ∧ V1 <: U1 ∧ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember (Arrow' V1 V2) as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs;intros.
  3 : inversion HeqV.
  - exists V1, V2;auto.
  - apply IHHs2 in HeqV;inversion HeqV;inversion H;clear HeqV H.
    destruct H0. apply IHHs1 in H;inversion H;inversion H1;clear H H1.
    exists x1, x2. inversion H2. inversion H1. clear H2 H1.
    split;destruct H0...
  - inversion HeqV;subst. exists S1, S2...
Qed.

Require Import Coq.Program.Equality.

Lemma canonical_forms_of_arrow_types : ∀Gamma s T1 T2,
  Gamma ⊢ s ∈ Arrow' T1 T2 →
  value' s →
  ∃x S1 s2,
     s = abs' x S1 s2.
Proof with eauto.
  intros Gamma s T1 T2 H. dependent induction H;intros H';subst...
  1 - 3 : inversion H'.
  apply sub_inversion_arrow in H0. destruct H0 as [U1 (U2, (H1, (H2, H3)))].
  apply IHhas_type' in H1...
Qed.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert := solve_by_inverts 1.

Lemma canonical_forms_of_Bool : ∀Gamma s,
  Gamma ⊢ s ∈ Bool' →
  value' s →
  s = tru' ∨ s = fls'.
Proof with eauto.
  intros Gamma s Hty Hv.
  remember Bool' as T.
  induction Hty; try solve_by_invert...
  subst;apply sub_inversion_Bool in H;subst...
Qed.

Theorem progress' : ∀t T,
     empty ⊢ t ∈ T →
     value' t ∨ ∃t', t ---> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  revert HeqGamma.
  induction Ht;
    intros HeqGamma; subst...
  -  inversion H.
  - right.
    destruct IHHt1; subst...
    + destruct IHHt2; subst...
      * destruct (canonical_forms_of_arrow_types empty t1 T1 T2)
          as [x [S1 [t12 Heqt1]]]...
        subst. exists ([x:=t2]t12)...
      * inversion H0 as [t2' Hstp]. exists (app' t1 t2')...
    + inversion H as [t1' Hstp]. exists (app' t1' t2)...
  - right.
    destruct IHHt1.
    + eauto.
    + assert (t1 = tru' ∨ t1 = fls')
        by (eapply canonical_forms_of_Bool; eauto).
      inversion H0; subst...
    + inversion H. rename x into t1'. eauto.
Qed.

Lemma typing_inversion_abs : ∀Gamma x S1 t2 T,
     Gamma ⊢ (abs' x S1 t2) ∈ T →
     ∃S2,
       Arrow' S1 S2 <: T
       ∧ (x ⊢> S1 ; Gamma) ⊢ t2 ∈ S2.
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember (abs' x S1 t2) as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  - (* T_Abs *)
    exists T12...
  - (* T_Sub *)
    destruct IHhas_type' as [S2 [Hsub Hty]]...
  Qed.

Lemma typing_inversion_var : ∀Gamma x T,
  Gamma ⊢ (var' x) ∈ T →
  exists S,
    Gamma x = Some S ∧ S <: T.
Proof with eauto.
  intros Gamma x T Hty.
  remember (var' x) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  - (* T_Var *)
    exists T...
  - (* T_Sub *)
    destruct IHHty as [U [Hctx HsubU]]... Qed.

Lemma typing_inversion_app : ∀Gamma t1 t2 T2,
  Gamma ⊢ (app' t1 t2) ∈ T2 →
  exists T1,
    Gamma ⊢ t1 ∈ (Arrow' T1 T2) ∧
    Gamma ⊢ t2 ∈ T1.
Proof with eauto.
  intros Gamma t1 t2 T2 Hty.
  remember (app' t1 t2) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  - (* T_App *)
    exists T1...
  - (* T_Sub *)
    destruct IHHty as [U1 [Hty1 Hty2]]...
Qed.

Lemma typing_inversion_true : ∀Gamma T,
  Gamma ⊢ tru' ∈ T →
  Bool' <: T.
Proof with eauto.
  intros Gamma T Htyp. remember tru' as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_false : ∀Gamma T,
  Gamma ⊢ fls' ∈ T →
  Bool' <: T.
Proof with eauto.
  intros Gamma T Htyp. remember fls' as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_if : ∀Gamma t1 t2 t3 T,
  Gamma ⊢ (test' t1 t2 t3) ∈ T →
  Gamma ⊢ t1 ∈ Bool'
  ∧ Gamma ⊢ t2 ∈ T
  ∧ Gamma ⊢ t3 ∈ T.
Proof with eauto.
  intros Gamma t1 t2 t3 T Hty.
  remember (test' t1 t2 t3) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  - (* T_Test *)
    auto.
  - (* T_Sub *)
    destruct (IHHty H0) as [H1 [H2 H3]]...
Qed.

Lemma typing_inversion_unit : ∀Gamma T,
  Gamma ⊢ unit ∈ T →
    Unit <: T.
Proof with eauto.
  intros Gamma T Htyp. remember unit as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

Lemma abs_arrow : ∀x S1 s2 T1 T2,
  empty ⊢ (abs' x S1 s2) ∈ (Arrow' T1 T2) →
     T1 <: S1
  ∧ (x ⊢> S1 ; empty) ⊢ s2 ∈ T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  inversion Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  inversion Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  inversion Heq; subst... Qed.

Inductive appears_free_in : string → tms → Prop :=
  | afi_var : ∀x,
      appears_free_in x (var' x)
  | afi_app1 : ∀x t1 t2,
      appears_free_in x t1 → appears_free_in x (app' t1 t2)
  | afi_app2 : ∀x t1 t2,
      appears_free_in x t2 → appears_free_in x (app' t1 t2)
  | afi_abs : ∀x y T11 t12,
        y ≠ x →
        appears_free_in x t12 →
        appears_free_in x (abs' y T11 t12)
  | afi_test1 : ∀x t1 t2 t3,
      appears_free_in x t1 →
      appears_free_in x (test' t1 t2 t3)
  | afi_test2 : ∀x t1 t2 t3,
      appears_free_in x t2 →
      appears_free_in x (test' t1 t2 t3)
  | afi_test3 : ∀x t1 t2 t3,
      appears_free_in x t3 →
      appears_free_in x (test' t1 t2 t3)
.

Hint Constructors appears_free_in.

Theorem beq_string_refl : ∀ s, true = beq_string s s. 
Proof. 
  intros s. unfold beq_string. destruct (string_dec s s) as [|Hs]. 
  - reflexivity.   
  - destruct Hs. reflexivity. 
Qed.

Theorem beq_string_false_iff : ∀ x y : string,   beq_string x y = false ↔ x ≠ y. 
Proof. 
  intros x y. rewrite <- beq_string_true_iff. 
  rewrite not_true_iff_false. reflexivity. 
Qed.

Theorem false_beq_string : ∀ x y : string, x ≠ y → beq_string x y = false. 
Proof. 
  intros x y. rewrite beq_string_false_iff. 
  intros H. apply H. 
Qed.

Lemma context_invariance : ∀Gamma Gamma' t S,
     Gamma ⊢ t ∈ S →
     (∀x, appears_free_in x t → Gamma x = Gamma' x) →
     Gamma' ⊢ t ∈ S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  induction H;
    intros Gamma' Heqv...
  - (* T_Var *)
    apply T_Var... rewrite <- Heqv...
  - (* T_Abs *)
    apply T_Abs... apply IHhas_type'. intros x0 Hafi.
    unfold update, t_update. destruct (eqb_spec x x0)...
    subst. rewrite <- beq_string_refl...
    specialize (false_beq_string _ _ n);intros;rewrite H0...
  - (* T_Test *)
    apply T_Test'...
Qed.

Lemma free_in_context : ∀x t T Gamma,
   appears_free_in x t →
   Gamma ⊢ t ∈ T →
   ∃T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp;
      subst; inversion Hafi; subst...
  - (* T_Abs *)
    destruct (IHHtyp H4) as [T Hctx]. exists T.
    unfold update, t_update in Hctx.
    rewrite <- beq_string_false_iff in H2.
    rewrite H2 in Hctx... Qed.

Lemma substitution_preserves_typing : ∀Gamma x U v t S,
     (x ⊢> U ; Gamma) ⊢ t ∈ S →
     empty ⊢ v ∈ U →
     Gamma ⊢ [x:=v]t ∈ S.
Proof with eauto.
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent S. generalize dependent Gamma.
  induction t; intros; simpl.
  - (* var *)
    rename s into y.
    destruct (typing_inversion_var _ _ _ Htypt)
        as [T [Hctx Hsub]].
    unfold update, t_update in Hctx.
    destruct (eqb_spec x y) as [Hxy|Hxy]; eauto;
    subst. rewrite <- beq_string_refl in *.
    inversion Hctx; subst. clear Hctx.
    apply context_invariance with empty...
    intros x Hcontra.
    destruct (free_in_context _ _ S empty Hcontra)
        as [T' HT']...
    inversion HT'.
    specialize (false_beq_string _ _ Hxy);intros;rewrite H in *...
  - (* app *)
    destruct (typing_inversion_app _ _ _ _ Htypt)
        as [T1 [Htypt1 Htypt2]].
    eapply T_App...
  - (* abs *)
    rename s into y. rename t into T1.
    destruct (typing_inversion_abs _ _ _ _ _ Htypt)
      as [T2 [Hsub Htypt2]].
    apply T_Sub with (Arrow' T1 T2)... apply T_Abs...
    destruct (eqb_spec x y) as [Hxy|Hxy].
    + (* x=y *)
      eapply context_invariance...
      subst.
      intros x Hafi. unfold update, t_update.
      destruct (eqb_spec y x);subst. rewrite <- beq_string_refl in *...
      specialize (false_beq_string _ _ n);intros;rewrite H in *...
    + (* x<>y *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_spec y z)...
      subst. rewrite <- beq_string_refl...
      specialize (false_beq_string _ _ Hxy);intros;rewrite H in *...
      rewrite <- beq_string_false_iff in Hxy.
      specialize (false_beq_string _ _ n);intros;rewrite H in *...
  - (* tru *)
      assert (Bool' <: S)
        by apply (typing_inversion_true _ _ Htypt)...
  - (* fls *)
      assert (Bool' <: S)
        by apply (typing_inversion_false _ _ Htypt)...
  - (* test *)
    assert ((x ⊢> U ; Gamma) ⊢ t1 ∈ Bool'
         ∧ (x ⊢> U ; Gamma) ⊢ t2 ∈ S
         ∧ (x ⊢> U ; Gamma) ⊢ t3 ∈ S)
      by apply (typing_inversion_if _ _ _ _ _ Htypt).
    inversion H as [H1 [H2 H3]].
    apply IHt1 in H1. apply IHt2 in H2. apply IHt3 in H3.
    auto.
  - (* unit *)
    assert (Unit <: S)
      by apply (typing_inversion_unit _ _ Htypt)...
Qed.

Theorem preservation' : ∀t t' T,
     empty ⊢ t ∈ T →
     t ---> t' →
     empty ⊢ t' ∈ T.
Proof with eauto.
  intros t t' T HT.
  remember empty as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  induction HT;
    intros t' HeqGamma HE; subst; inversion HE; subst...
  - (* T_App *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T...
Qed.

