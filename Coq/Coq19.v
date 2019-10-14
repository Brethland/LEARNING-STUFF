(*
  This is exericses for <Software Foundations> CH12.
  Author : Brethland, Late 2019
*)

Require Import Coq.Bool.Bool. 
Require Import Coq.Arith.Arith. 
Require Import Coq.Arith.EqNat. 
Require Import Coq.omega.Omega. 
Require Import Coq.Lists.List. 
Require Import Unicode.Utf8.
Require Export Coq.Strings.String. 
Require Import Setoid.
Import ListNotations.

Definition beq_string x y :=   if string_dec x y then true else false. 

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

Definition total_map (A:Type) := string → A.

Definition t_empty {A:Type} (v : A) : total_map A :=   (fun _ => v).

Definition t_update {A:Type} (m : total_map A) (x : string) (v : A) := 
  fun x' => if beq_string x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition state := total_map nat. 

Module EXP_TRY.

Inductive aexp : Type :=
  | ANum : nat → aexp   
  | APlus : aexp → aexp → aexp   
  | AMinus : aexp → aexp → aexp   
  | AMult : aexp → aexp → aexp. 

Inductive bexp : Type :=   
  | BTrue : bexp   
  | BFalse : bexp   
  | BEq : aexp → aexp → bexp   
  | BLe : aexp → aexp → bexp   
  | BNot : bexp → bexp   
  | BAnd : bexp → bexp → bexp.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.


Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Theorem optimize_0plus_sound: ∀a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros.
  induction a.
  - simpl. auto.
  - simpl. rewrite <- IHa1.
    rewrite <- IHa2.
    fold aeval. destruct a1.
    + simpl. destruct n. simpl. auto.
      simpl. auto.
    + auto.
    + auto.
    + auto.
  - simpl. rewrite <- IHa1.
    rewrite <- IHa2. auto.
  - simpl. rewrite <- IHa1.
    rewrite <- IHa2. auto.
Qed.

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot (optimize_0plus_b b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Theorem optimize_0plus_b_sound : ∀b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  induction b;
  try simpl;auto; 
  try repeat rewrite optimize_0plus_sound;auto;
  try try rewrite <- IHb1;try rewrite <- IHb2;try rewrite IHb;auto.
Qed.

Fixpoint optimize_and_false (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq a1 a2
  | BLe a1 a2 => BLe a1 a2
  | BNot b1 => BNot (optimize_and_false b1)
  | BAnd b1 b2 => match b1 with 
                  | BFalse => BFalse
                  | _ => BAnd (optimize_and_false b1) (optimize_and_false b2)
                  end
  end.

Lemma andb_same : forall a b c, a = b -> a && c = b && c.
Proof.
  intros. destruct a;
  try destruct b;inversion H;auto.
Qed.

Lemma optimize_and_false_bound : forall b, beval (optimize_and_false b) = beval b.
Proof.
  induction b;
  try simpl;auto;
  try rewrite IHb;auto.
  - induction b1; try (simpl;try rewrite <- IHb1;try rewrite <- IHb2;auto).
    +  simpl in IHb1. rewrite IHb1. auto.
    +  simpl in IHb1. apply andb_same. apply IHb1.
Qed.

Module aevalR_first_try.
Inductive aevalR : aexp → nat → Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 →
      aevalR e2 n2 →
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 →
      aevalR e2 n2 →
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 →
      aevalR e2 n2 →
      aevalR (AMult e1 e2) (n1 * n2).

Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.
End aevalR_first_try.

Reserved Notation "e '\\' n" (at level 90, left associativity).
Inductive aevalR : aexp → nat → Prop :=
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) → (e2 \\ n2) → (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) → (e2 \\ n2) → (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) → (e2 \\ n2) → (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.

Theorem aeval_iff_aevalR' : ∀a n,
  (a \\ n) ↔ aeval a = n.
Proof.
  split.
  - intros H; induction H; subst; reflexivity.
  - generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

Inductive bevalR: bexp → bool → Prop :=
  | E_BTrue :  bevalR BTrue  true
  | E_BFalse : bevalR BFalse false
  | E_BEq (a1 a2 : aexp) (n1 n2 : nat) : (a1 \\ n1) -> (a2 \\ n2) -> bevalR (BEq a1 a2) (n1  =? n2)
  | E_BLe (a1 a2 : aexp) (n1 n2 : nat) : (a1 \\ n1) -> (a2 \\ n2) -> bevalR (BLe a1 a2) (n1 <=? n2)
  | E_BNot (b : bexp) (m : bool) : bevalR b m -> bevalR (BNot b) (negb m)
  | E_BAnd (b1 b2 : bexp) (m1 m2 : bool) : bevalR b1 m1 -> bevalR b2 m2 -> bevalR (BAnd b1 b2) (andb m1 m2).

Lemma beval_iff_bevalR : ∀b bv,
  bevalR b bv ↔ beval b = bv.
Proof.
  split.
  - intros H; induction H; try (subst; auto);
    try (apply aeval_iff_aevalR' in H;
         apply aeval_iff_aevalR' in H0;
         subst; auto).
  - generalize dependent bv;
    induction b;
    try (intros; subst; constructor; apply aeval_iff_aevalR'; auto);
    try (intros; simpl in H; subst; constructor; try apply IHb; try apply IHb1; try apply IHb2; auto).
Qed.

End EXP_TRY.

Inductive aexp : Type :=
  | AId : string → aexp
  | ANum : nat → aexp   
  | APlus : aexp → aexp → aexp   
  | AMinus : aexp → aexp → aexp   
  | AMult : aexp → aexp → aexp. 

Inductive bexp : Type :=   
  | BTrue : bexp   
  | BFalse : bexp   
  | BEq : aexp → aexp → bexp   
  | BLe : aexp → aexp → bexp   
  | BNot : bexp → bexp   
  | BAnd : bexp → bexp → bexp.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.
Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.
Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x ≤ y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.
Definition example_aexp := (3 + (X * 2))%imp : aexp.
Definition example_bexp := (true && ~(X ≤ 4))%imp : bexp.

Definition empty_st := (_ !-> 0).
Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

Example aexp1 :
    aeval (X !-> 5) (3 + (X * 2))%imp
  = 13.
Proof. reflexivity. Qed.

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
(*   | CFor (c1 c2 c3 : com) (b : bexp) *)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.
(* Notation "'FOR' c1 ';;;' b ';;;' c2 'DO' c3 'FI'" :=
  (CFor c1 c2 c3 b) (at level 80, right associativity) : imp_scope. *)

Open Scope imp_scope.
Fixpoint ceval_fun_no_while (st : state) (c : com)
                          : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        (x !-> (aeval st a1) ; st)
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st (* bogus *)
(*    |  FOR c1 ;;; b ;;; c2 DO c3 FI =>
       st *)
  end.
Close Scope imp_scope.

Reserved Notation "st '=[' c ']⇒' st'"
                  (at level 40).

Inductive ceval : com → state → state → Prop :=
  | E_Skip : ∀st,
      st =[ SKIP ]⇒ st
  | E_Ass : ∀st a1 n x,
      aeval st a1 = n →
      st =[ x ::= a1 ]⇒ (x !-> n ; st)
  | E_Seq : ∀c1 c2 st st' st'',
      st =[ c1 ]⇒ st' →
      st' =[ c2 ]⇒ st'' →
      st =[ c1 ;; c2 ]⇒ st''
  | E_IfTrue : ∀st st' b c1 c2,
      beval st b = true →
      st =[ c1 ]⇒ st' →
      st =[ IFB b THEN c1 ELSE c2 FI ]⇒ st'
  | E_IfFalse : ∀st st' b c1 c2,
      beval st b = false →
      st =[ c2 ]⇒ st' →
      st =[ IFB b THEN c1 ELSE c2 FI ]⇒ st'
  | E_WhileFalse : ∀b st c,
      beval st b = false →
      st =[ WHILE b DO c END ]⇒ st
  | E_WhileTrue : ∀st st' st'' b c,
      beval st b = true →
      st =[ c ]⇒ st' →
      st' =[ WHILE b DO c END ]⇒ st'' →
      st =[ WHILE b DO c END ]⇒ st''
(*   | E_ForFalse : forall b st st' c1 c2 c3,
      st =[ c1 ]⇒ st' ->
      beval st b = false ->
      st =[ FOR c1 ;;; b ;;; c2 DO c3 FI]⇒ st'
  | E_ForTrue : forall st st' st'' st0 c1 c2 c3 b,
      st =[ c1 ]⇒ st' ->
      beval st b = true ->
      st' =[ c3;;c2 ]⇒ st'' ->
      st'' =[ FOR c1 ;;; b ;;; c2 DO c3 FI]⇒ st0 ->
      st =[ FOR c1 ;;; b ;;; c2 DO c3 FI]⇒ st0 *)

  where "st =[ c ]⇒ st'" := (ceval c st st').

Example ceval_example1:
  empty_st =[
     X ::= 2;;
     IFB X ≤ 1
       THEN Y ::= 3
       ELSE Z ::= 4
     FI
  ]⇒ (Z !-> 4 ; X !-> 2).
Proof.
  apply E_Seq with (X !-> 2).
  - apply E_Ass. auto.
  - apply E_IfFalse.
    + auto.
    + apply E_Ass. auto.
Qed.

Example ceval_example2:
  empty_st =[
    X ::= 0;; Y ::= 1;; Z ::= 2
  ]⇒ (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  apply E_Seq with (X !-> 0).
  - apply E_Ass. auto.
  - apply E_Seq with (Y !-> 1 ; X !-> 0).
    + apply E_Ass. auto.
    + apply E_Ass. auto.
Qed.

Definition pup_to_n : com :=
  (Y ::= 0 ;;
  WHILE ~(X = 0) DO
    Y ::= Y + X ;;
    X ::= X - 1
  END)%imp.

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]⇒ (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  unfold pup_to_n.
  apply E_Seq with (Y !-> 0 ; X !-> 2).
  - apply E_Ass. auto.
  - apply E_WhileTrue with (X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
    + auto.
    + apply E_Seq with (Y !-> 2; Y !-> 0; X !-> 2). apply E_Ass. auto.
      apply E_Ass. auto.
    + apply E_WhileTrue with (X !-> 0; Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
      ++ auto.
      ++ apply E_Seq with (Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2). apply E_Ass. auto.
         apply E_Ass. auto.
      ++ apply E_WhileFalse. auto.
Qed.

Theorem ceval_deterministic: ∀c st st1 st2,
     st =[ c ]⇒ st1 →
     st =[ c ]⇒ st2 →
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2. generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - auto.
  - auto.
  - assert (st' = st'0) as EQ1.
    { apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - apply IHE1. auto.
  - rewrite H in H5. inversion H5.
  - rewrite H in H5. inversion H5.
  - apply IHE1. auto.
  - auto.
  - rewrite H in H2. inversion H2.
  - rewrite H in H4. inversion H4.
  - assert (st' = st'0) as EQ1.
    { apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
Qed.

Definition plus2 : com :=
  X ::= X + 2.
Definition XtimesYinZ : com :=
  Z ::= X * Y.
Definition subtract_slowly_body : com :=
  Z ::= Z - 1 ;;
  X ::= X - 1.

Definition subtract_slowly : com :=
  (WHILE ~(X = 0) DO
    subtract_slowly_body
  END)%imp.
Definition subtract_3_from_5_slowly : com :=
  X ::= 3 ;;
  Z ::= 5 ;;
  subtract_slowly.

Definition loop : com :=
  WHILE true DO
    SKIP
  END.

Lemma t_update_eq : ∀(A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update. rewrite <- beq_string_refl.
  auto.
Qed.

Theorem plus2_spec : ∀st n st',
  st X = n →
  st =[ plus2 ]⇒ st' →
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq. Qed.

Lemma XtimesYinZ_spec : forall st n m st',
  st X = n -> st Y = m -> st =[ XtimesYinZ ]⇒  st' ->
    st' Z = n * m.
Proof.
  intros.
  inversion H1. subst. simpl. apply t_update_eq.
Qed.

Theorem loop_never_stops : ∀st st',
  ~(st =[ loop ]⇒ st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE true DO SKIP END)%imp as loopdef
           eqn:Heqloopdef.
  induction contra;
  try (subst; inversion Heqloopdef).
  - subst. inversion H.
  - subst. apply IHcontra2. assumption.
Qed.

Open Scope imp_scope.
Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP =>
      true
  | _ ::= _ =>
      true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END =>
      false
  end.
Close Scope imp_scope.

Inductive no_whilesR : com -> Prop :=
  | sk_now : no_whilesR SKIP
  | ass_now : forall X n, no_whilesR (X ::= n)
  | seq_now : forall c1 c2, no_whilesR c1 -> no_whilesR c2
                            -> no_whilesR (c1 ;; c2)
  | if_now : forall c1 c2 b, no_whilesR c1 -> no_whilesR c2
                            -> no_whilesR (IFB b THEN c1 ELSE c2 FI).

Lemma andb_oj : forall a b , andb a b = true -> a = true /\ b = true.
Proof.
  intros. destruct a;destruct b;split;auto.
Qed.
 
Theorem no_whiles_eqv:
   ∀c, no_whiles c = true ↔ no_whilesR c.
Proof.
  intros. split.
  - intros. induction c;
    try (constructor;simpl in H; apply andb_oj in H;
    destruct H);
    try (apply IHc1 in H;
    apply H);
    try (apply IHc2 in H0;
    apply H0).
    inversion H.
  - intros. induction H;
    try (constructor;simpl;subst;auto);
    try (simpl;rewrite IHno_whilesR1;rewrite IHno_whilesR2;
    auto).
Qed.

Lemma no_whiles_trminating : forall c st,
  no_whilesR c -> exists st', st =[ c ]⇒ st'.
Proof.
  intros. generalize dependent st.
  induction c;intros.
  - exists st. constructor.
  - exists (x !-> aeval st a; st).
    apply E_Ass. auto.
  - inversion H.
    remember (IHc1 H2 st) as H'.
    destruct H'.
    remember (IHc2 H3 x) as H''.
    destruct H''.
    exists x0. apply E_Seq with x.
    auto. auto.
  - inversion H. subst.
    remember (beval st b) as sb.
    remember (IHc1 H2 st) as H'.
    destruct H'.
    remember (IHc2 H4 st) as H''.
    destruct H''.
    destruct sb.
    + exists x. constructor. auto. auto.
    + exists x0. apply E_IfFalse. auto. auto.
  - inversion H.
Qed.

Inductive sinstr : Type := 
  | SPush : nat → sinstr 
  | SLoad : string → sinstr 
  | SPlus : sinstr 
  | SMinus : sinstr 
  | SMult : sinstr.

Fixpoint s_execute (st : state) (stack : list nat)
  (prog : list sinstr) : list nat :=
  match prog with
  | [] => stack
  | p :: ps => match p with
                | SPush n => s_execute st (n :: stack) ps
                | SLoad s => s_execute st ((st s) :: stack) ps
                | SPlus => match stack with
                            | n :: (m :: ss) => s_execute st ((n + m) :: ss) ps
                            | _ => s_execute st stack ps
                            end
                | SMinus => match stack with
                            | n :: (m :: ss) => s_execute st ((m - n) :: ss) ps
                            | _ => s_execute st stack ps
                            end
                | SMult => match stack with
                            | n :: (m :: ss) => s_execute st ((n * m) :: ss) ps
                            | _ => s_execute st stack ps
                            end
                end
  end.

Example s_execute1 : s_execute empty_st [] 
  [SPush 5; SPush 3; SPush 1; SMinus] = [2; 5].
Proof. simpl. auto. Qed.

Example s_execute2 : s_execute ( X !-> 3 ) [3;4]
  [SPush 4; SLoad X; SMult; SPlus] = [15; 4].
Proof. simpl. auto. Qed.

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | AId s => [ SLoad s ]
  | ANum n => [ SPush n ] 
  | APlus a1 a2 => s_compile a1 ++ s_compile a2 ++ [ SPlus ]
  | AMinus a1 a2 => s_compile a1 ++ s_compile a2 ++ [ SMinus ]
  | AMult a1 a2 => s_compile a1 ++ s_compile a2 ++ [ SMult ]
  end.

Example s_compile1 : s_compile (X - (2 * Y)) 
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus]. 
Proof. simpl. auto. Qed.

Theorem s_concat_app :
  forall (st : state) (p1 p2 : list sinstr) (l : list nat),
    s_execute st l (p1 ++ p2) = s_execute st (s_execute st l p1)  p2.
Proof.
  intros. generalize dependent l.
  induction p1.
  - simpl. auto.
  - intros. simpl. destruct a;try apply IHp1.
    + destruct l. apply IHp1.
      destruct l. apply IHp1. apply IHp1.
    + destruct l. apply IHp1.
      destruct l. apply IHp1. apply IHp1.
    + destruct l. apply IHp1.
      destruct l. apply IHp1. apply IHp1.
Qed.

Theorem s_compile_correct : forall (e : aexp) (st : state) (stack : list nat),
   s_execute st stack (s_compile e) = aeval st e :: stack.
  intros e st.
  induction e;intros; try auto.
  - simpl. repeat rewrite s_concat_app.
    rewrite IHe2. rewrite IHe1. rewrite plus_comm. auto.
  - simpl. repeat rewrite s_concat_app.
    rewrite IHe2. rewrite IHe1. auto.
  - simpl. repeat rewrite s_concat_app.
    rewrite IHe2. rewrite IHe1. rewrite mult_comm. auto.
Qed.

Theorem s_compile_correct_nil : ∀ (st : state) (e : aexp), 
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros. apply s_compile_correct.
Qed.

Module BreakImp.

Inductive com : Type :=
  | CSkip
  | CBreak
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']⇒' st' '/' s"
         (at level 40, st' at next level).

Inductive ceval : com → state → result → state → Prop :=
  | E_Skip : ∀st,
      st =[ SKIP ]⇒ st / SContinue
  | E_Break : forall st,
      st =[ BREAK ]⇒ st / SBreak
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]⇒ (x !-> n; st) / SContinue
  | E_Seq_Break : forall c1 c2 st st',
      st =[ c1 ]⇒ st' / SBreak ->
      st =[ c1;;c2 ]⇒ st' / SBreak
  | E_Seq_Continue : forall c1 c2 st st' st'' s,
      st =[ c1 ]⇒ st' / SContinue ->
      st =[ c2 ]⇒ st'' / s ->
      st =[ c1;;c2 ]⇒ st'' / s
  | E_IfTrue : ∀st st' b c1 c2 s,
      beval st b = true →
      st =[ c1 ]⇒ st' / s →
      st =[ IFB b THEN c1 ELSE c2 FI ]⇒ st' / s
  | E_IfFalse : ∀st st' b c1 c2 s,
      beval st b = false →
      st =[ c2 ]⇒ st' / s →
      st =[ IFB b THEN c1 ELSE c2 FI ]⇒ st' / s
  | E_WhileFalse : ∀b st c,
      beval st b = false →
      st =[ WHILE b DO c END ]⇒ st / SContinue
  | E_WhileTrue : ∀st st' st'' b c,
      beval st b = true →
      st =[ c ]⇒ st' / SContinue →
      st' =[ WHILE b DO c END ]⇒ st'' / SContinue →
      st =[ WHILE b DO c END ]⇒ st'' / SContinue
  | E_WhileTrue_Break : forall st st' b c,
      beval st b = true ->
      st =[ c ]⇒ st' / SBreak ->
      st =[ WHILE b DO c END ]⇒ st' / SContinue

  where "st '=[' c ']⇒' st' '/' s" := (ceval c st s st').

Theorem break_ignore : ∀c st st' s,
     st =[ BREAK ;; c ]⇒ st' / s →
     st = st'.
Proof.
  intros. inversion H.
  - subst. inversion H5. subst. auto.
  - subst. inversion H2.
Qed.

Theorem while_continue : ∀b c st st' s,
  st =[ WHILE b DO c END ]⇒ st' / s →
  s = SContinue.
Proof.
  intros. inversion H;try (subst;auto).
Qed.

Theorem while_stops_on_break : ∀b c st st',
  beval st b = true →
  st =[ c ]⇒ st' / SBreak →
  st =[ WHILE b DO c END ]⇒ st' / SContinue.
Proof.
  intros. constructor. auto. auto.
Qed.

Theorem while_break_true : ∀b c st st',
  st =[ WHILE b DO c END ]⇒ st' / SContinue →
  beval st' b = true →
  ∃st'', st'' =[ c ]⇒ st' / SBreak.
Proof.
  intros. remember (WHILE b DO c END) as loop.
  induction H;inversion Heqloop.
  - subst. rewrite H in H0. inversion H0.
  - subst. apply IHceval2. auto. auto.
  - subst. exists st. auto.
Qed.

(* Theorem ceval_deterministic_failed: ∀(c:com) st st1 st2 s1 s2,
     st =[ c ]⇒ st1 / s1 →
     st =[ c ]⇒ st2 / s2 →
     st1 = st2 ∧ s1 = s2.
Proof.
  induction c;intros.
  - inversion H; inversion H0. subst. auto.
  - inversion H; inversion H0. subst. auto.
  - inversion H; inversion H0. subst. auto.
  - inversion H; inversion H0.
    + specialize (IHc1 st st1 st2 SBreak SBreak). apply IHc1.
      auto. auto.
    + specialize (IHc1 st st1 st'0 SBreak SContinue H6 H9).
      destruct IHc1. inversion H15.
    + specialize (IHc1 st st' st2 SContinue SBreak H3 H13).
      destruct IHc1. inversion H15.
    + apply (IHc2 _ _ _ _ _ H7 H14).
  - inversion H; inversion H0.
    + subst. specialize (IHc1 st st1 st2 s1 s2).
      apply IHc1. auto. auto.
    + subst. rewrite H15 in H7. inversion H7.
    + subst. rewrite H15 in H7. inversion H7.
    + subst. specialize (IHc2 st st1 st2 s1 s2).
      apply IHc2. auto. auto.
  - remember (beval st b) as Heb. destruct Heb.
    + inversion H; inversion H0.
      ++ subst. rewrite <- HeqHeb in H12. inversion H12.
      ++ subst. rewrite H6 in H9. inversion H9.
      ++ subst. rewrite H6 in H9. inversion H9.
      ++ subst. rewrite H3 in H14. inversion H14.
      ++ subst. Admitted. *)

Theorem ceval_deterministic: ∀(c:com) st st1 st2 s1 s2,
     st =[ c ]⇒ st1 / s1 →
     st =[ c ]⇒ st2 / s2 →
     st1 = st2 ∧ s1 = s2.
Proof.
  intros.
  generalize dependent st2.
  generalize dependent s2.
  induction H; intros.
  - inversion H0. auto.
  - inversion H0. auto.
  - inversion H0. subst. auto.
  - inversion H0. subst. apply (IHceval _ _ H6).
    subst. specialize (IHceval _ _ H3). destruct IHceval. inversion H2.
  - inversion H1;subst.
    + specialize (IHceval1 _ _ H7). destruct IHceval1. inversion H3.
    + apply IHceval2, H8.
  - inversion H1.
    + subst. apply IHceval. auto.
    + subst. rewrite H in H8. inversion H8.
  - inversion H1.
    + subst. rewrite H in H8. inversion H8.
    + subst. apply IHceval. auto.
  - inversion H0.
    + subst. auto.
    + subst. rewrite H in H3. inversion H3.
    + subst. rewrite H in H3. inversion H3.
  - inversion H2;subst.
    + rewrite H in H8. inversion H8.
    + apply IHceval2. specialize (IHceval1 _ _ H6). destruct IHceval1. subst.
      auto.
    + specialize (IHceval1 _ _ H9). destruct IHceval1. inversion H4.
  - inversion H1;subst.
    + rewrite H in H7. inversion H7.
    + specialize (IHceval _ _ H5). destruct IHceval. inversion H3.
    + specialize (IHceval _ _ H8). intuition.
  (* But Why, induction on c doesn't work? *)
Qed.

End BreakImp.

Notation "'FOR' c1 ';' b ';' c2 'DO' c3 'END'" :=
  (CSeq c1 (CWhile b (CSeq c3 c2))) (at level 80, right associativity) : imp_scope.


