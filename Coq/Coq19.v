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
Import ListNotations.

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

