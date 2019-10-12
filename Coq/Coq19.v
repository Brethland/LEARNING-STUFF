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

