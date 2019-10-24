(* 
  Exercises for <Software Foundations> V2 CH1.
  Author : Brethland, Late 2019.
*)

From Coq Require Import omega.Omega.
From Coq Require Import Arith.Arith.
Require Import Coq.Logic.FunctionalExtensionality. 
Add LoadPath "C:\Users\ycy12\Documents\Workspace\LEARNING-STUFF\Coq".
Load Coq19.

Definition aequiv (a1 a2 : aexp) : Prop :=
  ∀(st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  ∀(st : state),
    beval st b1 = beval st b2.

Lemma aequiv_example : aequiv (X - X) 0.
Proof.
  intros st. simpl. omega.
Qed.

Theorem bequiv_example: bequiv (X - X = 0)%imp true.
Proof.
  intros st. unfold beval. rewrite aequiv_example. auto.
Qed.

Definition cequiv (c1 c2 : com) : Prop :=
  ∀(st st' : state),
    (st =[ c1 ]⇒ st') ↔ (st =[ c2 ]⇒ st').

Theorem skip_left : ∀c,
  cequiv
    (SKIP;; c)
    c.
Proof.
  intros. intros st st'.
  split.
  - intros. inversion H;subst. inversion H2;subst. auto.
  - intros. apply E_Seq with st. apply E_Skip. auto.
Qed.

Theorem skip_right : ∀c,
  cequiv
    (c ;; SKIP)
    c.
Proof.
  intros c st st'. split.
  - intros. inversion H;subst. inversion H5;subst. auto.
  - intros. apply E_Seq with st'. auto. apply E_Skip.
Qed.

Theorem TEST_true_simple : ∀c1 c2,
  cequiv
    (IFB true THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros c1 c2 st st'. split.
  - intros. inversion H;subst. auto. inversion H5.
  - intros. apply E_IfTrue. auto. auto.
Qed.

Theorem TEST_true: ∀b c1 c2,
  bequiv b BTrue →
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - inversion H; subst.
    + auto.
    + unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      inversion H5.
  - apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    rewrite Hb. reflexivity. 
Qed.

Theorem TEST_false : ∀b c1 c2,
  bequiv b BFalse →
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
Proof.
  intros b c1 c2 H. split.
  - intros. inversion H0;subst.
    + rewrite H in H6. inversion H6.
    + auto.
  - intros. apply E_IfFalse. rewrite H. auto. auto.
Qed.

Theorem swap_if_branches : ∀b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros b e1 e2 st st'. remember (beval st b) as Hb.
  generalize dependent st. generalize dependent st'.
  destruct Hb.
  - intros. split.
    + intros. inversion H;subst. apply E_IfFalse.
      simpl. rewrite <- HeqHb. auto. auto.
      rewrite H5 in HeqHb. inversion HeqHb.
    + intros. inversion H;subst. simpl in H5. rewrite <- HeqHb in H5.
      simpl in H5. inversion H5. apply E_IfTrue. auto. auto.
  - intros. split.
    + intros. inversion H;subst. rewrite H5 in HeqHb. inversion HeqHb.
      apply E_IfTrue. simpl. rewrite H5. auto. auto.
    + intros. inversion H;subst. apply E_IfFalse. auto. auto.
      simpl in H5. rewrite <- HeqHb in H5. simpl in H5. inversion H5.
Qed.

Theorem WHILE_false : ∀b c,
  bequiv b BFalse →
  cequiv
    (WHILE b DO c END)
    SKIP.
Proof.
  intros b c Hb. split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* E_WhileFalse *)
      apply E_Skip.
    + (* E_WhileTrue *)
      rewrite Hb in H2. inversion H2.
  - (* <- *)
    inversion H; subst.
    apply E_WhileFalse.
    rewrite Hb.
    reflexivity. Qed.

Lemma WHILE_true_nonterm : ∀b c st st',
  bequiv b BTrue →
  ~( st =[ WHILE b DO c END ]⇒ st' ).
Proof.
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END)%imp as cw eqn:Heqcw.
  induction H;
  inversion Heqcw; subst; clear Heqcw.
  - unfold bequiv in Hb.
    rewrite Hb in H. inversion H.
  - apply IHceval2. reflexivity. Qed.

Theorem WHILE_true : ∀b c,
  bequiv b true →
  cequiv
    (WHILE b DO c END)
    (WHILE true DO SKIP END).
Proof.
  intros b c H st st'. split. 
  - intros. simpl in H. apply (WHILE_true_nonterm b c st st') in H.
    apply H in H0. inversion H0.
  - intros. simpl in H. 
    remember (WHILE true DO SKIP END)%imp as cw eqn:Heqcw.
    induction H0;inversion Heqcw;subst;clear Heqcw.
    + inversion H0.
    + inversion H0_;subst. apply IHceval2. auto.
Qed.

Theorem loop_unrolling : ∀b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c ;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  intros b c st st'.
  split; intros Hce.
  - inversion Hce; subst.
    + apply E_IfFalse. assumption. apply E_Skip.
    + apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  - inversion Hce; subst.
    + inversion H5; subst.
      apply E_WhileTrue with (st' := st'0).
      assumption. assumption. assumption.
    + inversion H5; subst. apply E_WhileFalse. assumption. 
Qed.

Theorem seq_assoc : ∀c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  intros c1 c2 c3 st st'. split.
  - intros. inversion H;subst. inversion H2;subst.
    apply E_Seq with st'1. auto. apply E_Seq with st'0.
    auto. auto.
  - intros. inversion H;subst. inversion H5;subst.
    apply E_Seq with st'1. apply E_Seq with st'0. auto. auto. auto.
Qed.

Lemma beq_stringP : ∀ x y, reflect (x = y) (beq_string x y).
Proof.
  intros. destruct (beq_string x y) eqn:HS.
  - apply ReflectT. apply beq_string_true_iff. auto.
  - apply ReflectF. apply beq_string_false_iff. auto.
Qed.

Theorem t_update_same : ∀(A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros. apply functional_extensionality.
  intros. unfold t_update.
  destruct (beq_stringP x x0).
  - rewrite e. auto.
  - auto.
Qed.

Theorem identity_assignment : ∀x,
  cequiv
    (x ::= x)
    SKIP.
Proof.
  intros.
  split; intro H; inversion H; subst.
  - rewrite t_update_same.
    apply E_Skip.
  - assert (Hx : st' =[ x ::= x ]⇒ (x !-> st' x ; st')).
    { apply E_Ass. reflexivity. }
    rewrite t_update_same in Hx.
    apply Hx.
Qed.

Theorem assign_aequiv : ∀(x : string) e,
  aequiv x e →
  cequiv SKIP (x ::= e).
Proof.
  intros. split.
  - intros. assert (Hx : st' =[ x ::= e ]⇒ (x !-> st' x; st')).
    specialize (H st'). simpl in H. rewrite -> H. apply E_Ass. auto.
    rewrite t_update_same in Hx. inversion H0;subst. auto.
  - intros. inversion H0;subst. specialize (H st). simpl in H.
    rewrite <- H. rewrite t_update_same. apply E_Skip.
Qed.


