(*
  Exercises for <Software Foundations> V2 CH5.
  Author : Brethland, Late 2019.
*)

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

Lemma multistep_congr_2 : ∀t1 t2 t2',
     value t1 →
     t2 -->* t2' →
     P t1 t2 -->* P t1 t2'.
Proof.
  intros. induction H0;try constructor.
  apply multi_step with (P t1 y). econstructor;auto. auto.
Qed.

Lemma multistep_congr_1 : ∀t1 t1' t2,
     t1 -->* t1' →
     P t1 t2 -->* P t1' t2.
Proof.
  intros t1 t1' t2 H. induction H.
  - (* multi_refl *) apply multi_refl.
  - (* multi_step *) apply multi_step with (P y t2).
    + apply ST_Plus1. apply H.
    + apply IHmulti.
Qed.

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  induction t.
  - exists (C n).
    split.
    + apply multi_refl.
    + rewrite nf_same_as_value. apply v_const.
  - destruct IHt1 as [t1' [Hsteps1 Hnormal1]].
    destruct IHt2 as [t2' [Hsteps2 Hnormal2]].
    rewrite nf_same_as_value in Hnormal1.
    rewrite nf_same_as_value in Hnormal2.
    inversion Hnormal1 as [n1 H1].
    inversion Hnormal2 as [n2 H2].
    rewrite <- H1 in Hsteps1.
    rewrite <- H2 in Hsteps2.
    exists (C (n1 + n2)).
    split.
    + apply multi_trans with (P (C n1) t2).
      * apply multistep_congr_1. apply Hsteps1.
      * apply multi_trans with
        (P (C n1) (C n2)).
        { apply multistep_congr_2. apply v_const. apply Hsteps2. }
        apply multi_R. { apply ST_PlusConstConst. }
    + rewrite nf_same_as_value. apply v_const.
Qed.

Theorem eval__multistep : ∀t n,
  t ===> n → t -->* C n.
Proof.
  intros. induction H;try constructor.
  assert (P t1 t2 -->* P (C n1) t2).
  apply multistep_congr_1. auto.
  apply multi_trans with (P (C n1) t2). auto.
  assert (P (C n1) t2 -->* P (C n1) (C n2)).
  apply multistep_congr_2. constructor. auto.
  apply multi_trans with (P (C n1) (C n2)). auto.
  apply multi_R. constructor.
Qed.

Lemma step__eval : ∀t t' n,
     t ---> t' →
     t' ===> n →
     t ===> n.
Proof.
  intros t t' n Hs. generalize dependent n.
  induction Hs;intros.
  - inversion H. constructor;constructor.
  - inversion H;subst. apply (IHHs (n1)) in H2.
    constructor;auto.
  - inversion H0;subst. apply (IHHs (n2)) in H5.
    constructor;auto.
Qed.

Theorem multistep__eval : ∀t t',
  normal_form_of t t' → ∃n, t' = C n ∧ t ===> n.
Proof.
  intros. unfold normal_form_of in H. destruct H.
  unfold step_normal_form in H0. apply nf_same_as_value in H0.
  inversion H0. exists n. split. auto. induction H;subst. constructor.
  apply step__eval with y. auto. apply IHmulti. auto. auto.
Qed.

Theorem evalF_eval : ∀t n,
  evalF t = n ↔ t ===> n.
Proof.
  split.
  - generalize dependent n. induction t;intros.
    simpl in H;subst;constructor.
    simpl in H. remember (evalF t1) as n1. remember (evalF t2) as n2.
    specialize (IHt1 n1). specialize (IHt2 n2). 
    rewrite <- H. constructor. apply IHt1. auto. apply IHt2. auto.
  - intros. induction H. simpl. auto.
    simpl. subst. auto.
Qed.

Inductive aval : aexp → Prop :=
  | av_num : ∀n, aval (ANum n).

Reserved Notation " t '/' st '-->a' t' "
                  (at level 40, st at level 39).
Inductive astep : state → aexp → aexp → Prop :=
  | AS_Id : ∀st i,
      AId i / st -->a ANum (st i)
  | AS_Plus1 : ∀st a1 a1' a2,
      a1 / st -->a a1' →
      (APlus a1 a2) / st -->a (APlus a1' a2)
  | AS_Plus2 : ∀st v1 a2 a2',
      aval v1 →
      a2 / st -->a a2' →
      (APlus v1 a2) / st -->a (APlus v1 a2')
  | AS_Plus : ∀st n1 n2,
      APlus (ANum n1) (ANum n2) / st -->a ANum (n1 + n2)
  | AS_Minus1 : ∀st a1 a1' a2,
      a1 / st -->a a1' →
      (AMinus a1 a2) / st -->a (AMinus a1' a2)
  | AS_Minus2 : ∀st v1 a2 a2',
      aval v1 →
      a2 / st -->a a2' →
      (AMinus v1 a2) / st -->a (AMinus v1 a2')
  | AS_Minus : ∀st n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st -->a (ANum (minus n1 n2))
  | AS_Mult1 : ∀st a1 a1' a2,
      a1 / st -->a a1' →
      (AMult a1 a2) / st -->a (AMult a1' a2)
  | AS_Mult2 : ∀st v1 a2 a2',
      aval v1 →
      a2 / st -->a a2' →
      (AMult v1 a2) / st -->a (AMult v1 a2')
  | AS_Mult : ∀st n1 n2,
      (AMult (ANum n1) (ANum n2)) / st -->a (ANum (mult n1 n2))

    where " t '/' st '-->a' t' " := (astep st t t').
Reserved Notation " t '/' st '-->b' t' "
                  (at level 40, st at level 39).
Inductive bstep : state → bexp → bexp → Prop :=
| BS_Eq1 : ∀st a1 a1' a2,
    a1 / st -->a a1' →
    (BEq a1 a2) / st -->b (BEq a1' a2)
| BS_Eq2 : ∀st v1 a2 a2',
    aval v1 →
    a2 / st -->a a2' →
    (BEq v1 a2) / st -->b (BEq v1 a2')
| BS_Eq : ∀st n1 n2,
    (BEq (ANum n1) (ANum n2)) / st -->b
    (if (n1 =? n2) then BTrue else BFalse)
| BS_LtEq1 : ∀st a1 a1' a2,
    a1 / st -->a a1' →
    (BLe a1 a2) / st -->b (BLe a1' a2)
| BS_LtEq2 : ∀st v1 a2 a2',
    aval v1 →
    a2 / st -->a a2' →
    (BLe v1 a2) / st -->b (BLe v1 a2')
| BS_LtEq : ∀st n1 n2,
    (BLe (ANum n1) (ANum n2)) / st -->b
             (if (n1 <=? n2) then BTrue else BFalse)
| BS_NotStep : ∀st b1 b1',
    b1 / st -->b b1' →
    (BNot b1) / st -->b (BNot b1')
| BS_NotTrue : ∀st,
    (BNot BTrue) / st -->b BFalse
| BS_NotFalse : ∀st,
    (BNot BFalse) / st -->b BTrue
| BS_AndTrueStep : ∀st b2 b2',
    b2 / st -->b b2' →
    (BAnd BTrue b2) / st -->b (BAnd BTrue b2')
| BS_AndStep : ∀st b1 b1' b2,
    b1 / st -->b b1' →
    (BAnd b1 b2) / st -->b (BAnd b1' b2)
| BS_AndTrueTrue : ∀st,
    (BAnd BTrue BTrue) / st -->b BTrue
| BS_AndTrueFalse : ∀st,
    (BAnd BTrue BFalse) / st -->b BFalse
| BS_AndFalse : ∀st b2,
    (BAnd BFalse b2) / st -->b BFalse

where " t '/' st '-->b' t' " := (bstep st t t').

Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).
Open Scope imp_scope.
Inductive cstep : (com * state) → (com * state) → Prop :=
  | CS_AssStep : ∀st i a a',
      a / st -->a a' →
      (i ::= a) / st --> (i ::= a') / st
  | CS_Ass : ∀st i n,
      (i ::= (ANum n)) / st --> SKIP / (i !-> n ; st)
  | CS_SeqStep : ∀st c1 c1' st' c2,
      c1 / st --> c1' / st' →
      (c1 ;; c2) / st --> (c1' ;; c2) / st'
  | CS_SeqFinish : ∀st c2,
      (SKIP ;; c2) / st --> c2 / st
  | CS_IfStep : ∀st b b' c1 c2,
      b / st -->b b' →
      IFB b THEN c1 ELSE c2 FI / st
      -->
      (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_IfTrue : ∀st c1 c2,
      IFB BTrue THEN c1 ELSE c2 FI / st --> c1 / st
  | CS_IfFalse : ∀st c1 c2,
      IFB BFalse THEN c1 ELSE c2 FI / st --> c2 / st
  | CS_While : ∀st b c1,
      WHILE b DO c1 END / st
      -->
      (IFB b THEN c1;; WHILE b DO c1 END ELSE SKIP FI) / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).
Close Scope imp_scope.

Module CImp.
Inductive com : Type :=
  | CSkip : com
  | CAss : string → aexp → com
  | CSeq : com → com → com
  | CIf : bexp → com → com → com
  | CWhile : bexp → com → com
  | CPar : com → com → com. (* <--- NEW *)
Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" :=
  (CPar c1 c2) (at level 80, right associativity).
Inductive cstep : (com * state) → (com * state) → Prop :=
    (* Old part *)
  | CS_AssStep : ∀st i a a',
      a / st -->a a' →
      (i ::= a) / st --> (i ::= a') / st
  | CS_Ass : ∀st i n,
      (i ::= (ANum n)) / st --> SKIP / (i !-> n ; st)
  | CS_SeqStep : ∀st c1 c1' st' c2,
      c1 / st --> c1' / st' →
      (c1 ;; c2) / st --> (c1' ;; c2) / st'
  | CS_SeqFinish : ∀st c2,
      (SKIP ;; c2) / st --> c2 / st
  | CS_IfStep : ∀st b b' c1 c2,
      b /st -->b b' →
          (TEST b THEN c1 ELSE c2 FI) / st
      --> (TEST b' THEN c1 ELSE c2 FI) / st
  | CS_IfTrue : ∀st c1 c2,
      (TEST BTrue THEN c1 ELSE c2 FI) / st --> c1 / st
  | CS_IfFalse : ∀st c1 c2,
      (TEST BFalse THEN c1 ELSE c2 FI) / st --> c2 / st
  | CS_While : ∀st b c1,
          (WHILE b DO c1 END) / st
      --> (TEST b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st
    (* New part: *)
  | CS_Par1 : ∀st c1 c1' c2 st',
      c1 / st --> c1' / st' →
      (PAR c1 WITH c2 END) / st --> (PAR c1' WITH c2 END) / st'
  | CS_Par2 : ∀st c1 c2 c2' st',
      c2 / st --> c2' / st' →
      (PAR c1 WITH c2 END) / st --> (PAR c1 WITH c2' END) / st'
  | CS_ParDone : ∀st,
      (PAR SKIP WITH SKIP END) / st --> SKIP / st
  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).
Definition cmultistep := multi cstep.
Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).

Definition par_loop : com :=
  PAR
    Y ::= 1
  WITH
    WHILE Y = 0 DO
      X ::= X + 1
    END
  END.

Lemma par_body_n__Sn : ∀n st,
  st X = n ∧ st Y = 0 →
  par_loop / st -->* par_loop / (X !-> S n ; st).
Proof.
  intros. eapply multi_step.
  apply CS_Par2. apply CS_While.
  eapply multi_step.
  apply CS_Par2. apply CS_IfStep.
  apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2.
  apply CS_IfStep. apply BS_Eq.
  simpl. eapply multi_step.
  destruct H. assert (st Y =? 0 = true). apply beq_nat_true_iff. auto.
  rewrite H. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep. apply CS_AssStep.
  apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep. apply CS_AssStep.
  destruct H. rewrite e. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  unfold par_loop. replace (n + 1) with (S n). apply multi_refl.
  omega.
Qed.

Lemma par_body_n : ∀n st,
  st X = 0 ∧ st Y = 0 →
  ∃st',
    par_loop / st -->* par_loop / st' ∧ st' X = n ∧ st' Y = 0.
Proof.
  intros. induction n.
  - exists st. split. apply multi_refl. auto.
  - destruct IHn. destruct H0. exists (X !-> S n ; x). split.
    eapply multi_trans. apply H0. apply par_body_n__Sn. auto.
    unfold t_update. simpl. split. auto. destruct H1. auto.
Qed.

End CImp.

Definition stack := list nat.
Definition prog := list sinstr.
Inductive stack_step : state → prog * stack → prog * stack → Prop :=
  | SS_Push : ∀st stk n p',
    stack_step st (SPush n :: p', stk) (p', n :: stk)
  | SS_Load : ∀st stk i p',
    stack_step st (SLoad i :: p', stk) (p', st i :: stk)
  | SS_Plus : ∀st stk n m p',
    stack_step st (SPlus :: p', n::m::stk) (p', (m+n)::stk)
  | SS_Minus : ∀st stk n m p',
    stack_step st (SMinus :: p', n::m::stk) (p', (m-n)::stk)
  | SS_Mult : ∀st stk n m p',
    stack_step st (SMult :: p', n::m::stk) (p', (m*n)::stk).
Theorem stack_step_deterministic : ∀st,
  deterministic (stack_step st).
Proof.
  unfold deterministic. intros st x y1 y2 H1 H2.
  induction H1; inversion H2; reflexivity.
Qed.

Definition stack_multistep st := multi (stack_step st).

(* Leaving the correctness of compiler *)
  