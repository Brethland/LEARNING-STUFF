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

Lemma sym_cequiv : forall (c1 c2 : com), cequiv c1 c2 -> cequiv c2 c1. 
Proof.
  intros c1 c2 H st st'.
  symmetry. apply H.
Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com), cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv;intros c1 c2 c3 H1 H2 st st'. 
  apply iff_trans with (st =[ c2]⇒ st'). auto. auto.
Qed.

Theorem CAss_congruence : ∀x a1 a1',
  aequiv a1 a1' →
  cequiv (CAss x a1) (CAss x a1').
Proof.
  intros. split.
  - intros. inversion H0;subst. apply E_Ass.
    rewrite H. auto.
  - intros. inversion H0;subst. apply E_Ass.
    rewrite H. auto.
Qed.

Theorem CWhile_congruence : ∀b1 b1' c1 c1',
  bequiv b1 b1' → cequiv c1 c1' →
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  intros. split;intros.
  - remember (WHILE b1 DO c1 END)%imp as cwhile eqn: Heqw.
    induction H1;inversion Heqw;subst.
    + rewrite H in H1. apply E_WhileFalse. auto.
    + apply E_WhileTrue with st'. rewrite H in H1. auto.
      apply H0 in H1_. auto. auto.
  - remember (WHILE b1' DO c1' END)%imp as cwhile eqn: Heqw.
    induction H1;inversion Heqw;subst.
    + rewrite <- H in H1. apply E_WhileFalse. auto.
    + apply E_WhileTrue with st'. rewrite <- H in H1. auto.
      apply H0 in H1_. auto. auto.
Qed.

Theorem CSeq_congruence : ∀c1 c1' c2 c2',
  cequiv c1 c1' → cequiv c2 c2' →
  cequiv (c1;;c2) (c1';;c2').
Proof.
  split;intros; inversion H1;subst;apply H in H4;apply H0 in H7;
            apply E_Seq with st'0; auto; auto.
Qed.

Theorem CIf_congruence : ∀b b' c1 c1' c2 c2',
  bequiv b b' → cequiv c1 c1' → cequiv c2 c2' →
  cequiv (IFB b THEN c1 ELSE c2 FI)
         (IFB b' THEN c1' ELSE c2' FI).
Proof.
  intros. split;intros.
  - inversion H2;subst.
    + apply E_IfTrue. rewrite H in H8. auto.
      apply H0 in H9. auto.
    + apply E_IfFalse. rewrite H in H8. auto.
      apply H1 in H9. auto.
  - inversion H2;subst.
    + apply E_IfTrue. rewrite <- H in H8. auto.
      apply H0 in H9. auto.
    + apply E_IfFalse. rewrite <- H in H8. auto.
      apply H1 in H9. auto.
Qed.

Definition atrans_sound (atrans : aexp → aexp) : Prop :=
  ∀(a : aexp),
    aequiv a (atrans a).
Definition btrans_sound (btrans : bexp → bexp) : Prop :=
  ∀(b : bexp),
    bequiv b (btrans b).
Definition ctrans_sound (ctrans : com → com) : Prop :=
  ∀(c : com),
    cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | APlus a1 a2 =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2 =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then BTrue else BFalse
      | (a1', a2') =>
          BEq a1' a2'
      end
  | BLe a1 a2 =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then BTrue else BFalse
      | (a1', a2') =>
          BLe a1' a2'
      end
  | BNot b1 =>
      match (fold_constants_bexp b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2 =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Open Scope imp.
Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP =>
      SKIP
  | x ::= a =>
      x ::= (fold_constants_aexp a)
  | c1 ;; c2 =>
      (fold_constants_com c1) ;; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => IFB b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.
Close Scope imp.

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros. unfold aequiv. intros.
  induction a;simpl;try reflexivity;
  try (destruct (fold_constants_aexp a1);
       destruct (fold_constants_aexp a2);
       rewrite IHa1; rewrite IHa2; reflexivity).
Qed.

Lemma fold_constants_bexp_sound :
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros. unfold bequiv. intros.
  induction b;auto.
  - simpl.
    remember (fold_constants_aexp a) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a0) as a2' eqn:Heqa2'.
    replace (aeval st a) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a0) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1';destruct a2';try reflexivity.
    simpl.  destruct (n =? n0);reflexivity.
  - simpl.
    remember (fold_constants_aexp a) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a0) as a2' eqn:Heqa2'.
    replace (aeval st a) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a0) with (aeval st a2') by
        (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1';try reflexivity.
    destruct a2';try reflexivity.
    simpl. destruct (n <=? n0);reflexivity.
  - simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  -  simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.

Lemma fold_constant_com_bound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros. induction c;simpl.
  - unfold cequiv. intros. split;intros;apply H.
  - apply CAss_congruence. apply fold_constants_aexp_sound.
  - apply CSeq_congruence. apply IHc1. apply IHc2.
  - assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;try (apply CIf_congruence; assumption).
    + apply trans_cequiv with c1; try assumption. apply TEST_true. auto.
    + apply trans_cequiv with c2; try assumption. apply TEST_false. auto.
  - assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb; try (apply CWhile_congruence; assumption).
    + apply WHILE_true. auto.
    + apply WHILE_false. auto.
Qed.

Fixpoint optimize_0plus_aexp (e : aexp) : aexp :=
  match e with
  | ANum n => ANum n
  | AId x => AId x
  | APlus (ANum 0) e2 => optimize_0plus_aexp e2
  | APlus e1 e2 =>
    APlus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AMinus e1 e2 =>
    AMinus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AMult e1 e2 =>
    AMult (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  end.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BLe a1 a2 => BLe (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BNot b1 => BNot (optimize_0plus_bexp b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_bexp b1) (optimize_0plus_bexp b2)
  end.

Open Scope imp.
Fixpoint optimize_0plus_com (c : com) : com :=
  match c with
  | SKIP => SKIP
  | x ::= a => x ::= (optimize_0plus_aexp a)
  | c1 ;; c2 => (optimize_0plus_com c1) ;; (optimize_0plus_com c2)
  | IFB b THEN c1 ELSE c2 FI
    =>IFB (optimize_0plus_bexp b) THEN
          (optimize_0plus_com c1) ELSE (optimize_0plus_com c2) FI
  | WHILE b DO c END
    => WHILE (optimize_0plus_bexp b) DO (optimize_0plus_com c) END
  end.
Close Scope imp.

Lemma plus_equiv : forall (a b : aexp) (st : state), aeval st a + aeval st b
                                                       = aeval st (a + b).
Proof.
  intros. induction a;try reflexivity.  
Qed.

Lemma optimize_0plus_aexp_sound :
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound. unfold aequiv. intros.
  induction a; simpl; try reflexivity;
    try (destruct a1;rewrite IHa1;rewrite IHa2;reflexivity).
  destruct a1.
  - simpl. rewrite IHa2. auto.
  - destruct n.
    + simpl. rewrite IHa2. auto.
    + rewrite IHa2. auto.
  - rewrite IHa1. rewrite IHa2. apply (plus_equiv (optimize_0plus_aexp(a1_1 + a1_2)) (optimize_0plus_aexp(a2)) st).
  - rewrite IHa1. rewrite IHa2. apply (plus_equiv (optimize_0plus_aexp(a1_1 - a1_2)) (optimize_0plus_aexp(a2)) st).
  - rewrite IHa1. rewrite IHa2. apply (plus_equiv (optimize_0plus_aexp(a1_1 * a1_2)) (optimize_0plus_aexp(a2)) st).
Qed.

Lemma optimize_0plus_bexp_sound :
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. unfold bequiv. intros.
  induction b;simpl;try reflexivity;
  try (rewrite optimize_0plus_aexp_sound;
    rewrite (optimize_0plus_aexp_sound a0);
    auto);try (rewrite IHb;auto);
    try(rewrite IHb1;rewrite IHb2;auto).
Qed.

Lemma optimize_0plus_com_sound :
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. induction c;simpl;unfold cequiv.
  - intros. split;auto.
  - apply CAss_congruence. apply optimize_0plus_aexp_sound.
  - apply CSeq_congruence. apply IHc1. apply IHc2.
  - apply CIf_congruence. apply optimize_0plus_bexp_sound. apply IHc1. apply IHc2.
  - apply CWhile_congruence. apply optimize_0plus_bexp_sound. apply IHc.
Qed.

Definition optimizer (c : com) := optimize_0plus_com (fold_constants_com c).

Lemma optimizer_sound : ctrans_sound optimizer.
Proof.
  unfold ctrans_sound. unfold cequiv. unfold optimizer.
  intros. split.
  - intros;apply (optimize_0plus_com_sound (fold_constants_com c)).
    apply (fold_constant_com_bound c);auto.
  - intros;apply (optimize_0plus_com_sound (fold_constants_com c)) in H.
    apply fold_constant_com_bound in H. auto.
Qed.

Fixpoint subst_aexp (x : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | AId x' =>
      if beq_string x x' then u else AId x'
  | APlus a1 a2 =>
      APlus (subst_aexp x u a1) (subst_aexp x u a2)
  | AMinus a1 a2 =>
      AMinus (subst_aexp x u a1) (subst_aexp x u a2)
  | AMult a1 a2 =>
      AMult (subst_aexp x u a1) (subst_aexp x u a2)
  end.


Definition subst_equiv_property := ∀x1 x2 a1 a2,
  cequiv (x1 ::= a1;; x2 ::= a2)
         (x1 ::= a1;; x2 ::= subst_aexp x1 a1 a2).

Theorem subst_inequiv :
  ¬subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.
  remember (X ::= X + 1;;
            Y ::= X)%imp
      as c1.
  remember (X ::= X + 1;;
            Y ::= X + 1)%imp
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).
  remember (Y !-> 1 ; X !-> 1) as st1.
  remember (Y !-> 2 ; X !-> 1) as st2.
  assert (H1 : empty_st =[ c1 ]⇒ st1);
  assert (H2 : empty_st =[ c2 ]⇒ st2);
  try (subst;
       apply E_Seq with (st' := (X !-> 1));
       apply E_Ass; reflexivity).
  apply H in H1.
  assert (Hcontra : st1 = st2)
    by (apply (ceval_deterministic c2 empty_st); assumption).
  assert (Hcontra' : st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'. Qed.

Inductive var_not_used_in_aexp (x : string) : aexp → Prop :=
  | VNUNum : ∀n, var_not_used_in_aexp x (ANum n)
  | VNUId : ∀y, x ≠ y → var_not_used_in_aexp x (AId y)
  | VNUPlus : ∀a1 a2,
      var_not_used_in_aexp x a1 →
      var_not_used_in_aexp x a2 →
      var_not_used_in_aexp x (APlus a1 a2)
  | VNUMinus : ∀a1 a2,
      var_not_used_in_aexp x a1 →
      var_not_used_in_aexp x a2 →
      var_not_used_in_aexp x (AMinus a1 a2)
  | VNUMult : ∀a1 a2,
      var_not_used_in_aexp x a1 →
      var_not_used_in_aexp x a2 →
      var_not_used_in_aexp x (AMult a1 a2).

Theorem t_update_neq : ∀(A : Type) (m : total_map A) x1 x2 v,
    x1 ≠ x2 →
    (x1 !-> v ; m) x2 = m x2.
Proof.
  intros.
  unfold t_update. apply beq_string_false_iff in H.
  rewrite H. auto.
Qed.


Lemma aeval_weakening : ∀x st a ni,
  var_not_used_in_aexp x a →
  aeval (x !-> ni ; st) a = aeval st a.
Proof.
  intros. induction H;try reflexivity;try simpl;
  try (rewrite IHvar_not_used_in_aexp1;rewrite IHvar_not_used_in_aexp2;auto).
  apply t_update_neq. auto.
Qed.
  
Lemma cequiv_trans : forall (c1 c2 c3 : com), cequiv c1 c2 -> cequiv c3 c2 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros.
  apply (@iff_trans (st=[ c1 ]⇒st') (st=[ c2 ]⇒st')).
  apply H.  symmetry. apply H0.
Qed.
  
Theorem inequiv_exercise:
  ¬cequiv (WHILE true DO SKIP END) SKIP.
Proof.
  unfold not. intros.
  (*assert(H' : cequiv (WHILE false DO SKIP END) SKIP).
  apply WHILE_false. simpl. unfold bequiv. auto.*)
  (*assert(Contra: cequiv (WHILE true DO SKIP END) (WHILE false DO SKIP END)).
  apply (cequiv_trans _ _ _ H H').*)
  (*apply (CWhile_congruence_inv BTrue BFalse) in Contra.*)
  apply loop_never_stops with empty_st empty_st.
  unfold loop. apply H. constructor.
Qed.  

Definition subst_equiv_property' := ∀x1 x2 a1 a2,
  var_not_used_in_aexp x1 a1 -> cequiv (x1 ::= a1;; x2 ::= a2)
         (x1 ::= a1;; x2 ::= subst_aexp x1 a1 a2).

Theorem swap_noninterfering_assignments: ∀l1 l2 a1 a2,
  l1 ≠ l2 →
  var_not_used_in_aexp l1 a2 →
  var_not_used_in_aexp l2 a1 →
  cequiv
    (l1 ::= a1;; l2 ::= a2)
    (l2 ::= a2;; l1 ::= a1).
Proof.
  intros. 

  (* LEAVING EXTENDED EXERCISES AND NODETERMINISTIC IMP*)
