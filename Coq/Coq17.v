(*
  This is exercises for <Software Foundations> CH10.
  Author : Brethland
*)

Require Import Coq.Arith.Arith. 
Require Import Coq.Bool.Bool. 
Require Export Coq.Strings.String. 
Require Import Coq.Logic.FunctionalExtensionality. 
Require Import Coq.Lists.List.
Require Import Unicode.Utf8.
Require Import Setoid.
Require Import PeanoNat.
Require Import Peano.
Require Import Arith.
Require Import List.

Theorem plus_one_r' : ∀ n:nat,   n + 1 = S n. 
Proof.
  apply nat_ind.
  - simpl. auto.
  - simpl. intros. rewrite H. auto.
Qed.

Inductive yesno : Type :=   
  | yes : yesno   
  | no : yesno.

Inductive byntree : Type :=  
  | bempty : byntree  
  | bleaf : yesno → byntree  
  | nbranch : yesno → byntree → byntree → byntree.

Check byntree_ind.

Inductive ExSet : Type := 
  | con1 : bool -> ExSet
  | con2 : nat -> ExSet -> ExSet.

Check ExSet_ind.

Inductive tree {X:Type} : Type :=   
  | leaf : X → tree
  | node : tree → tree → tree. 

Check tree_ind.

Inductive mytype (X : Type) : Type :=
  | constr1 : X -> mytype X
  | constr2 : nat -> mytype X
  | constr3 : mytype X -> nat -> mytype X.

Check mytype_ind.

Inductive foo (X Y : Type) : Type :=
  | bar : X -> foo X Y
  | baz : Y -> foo X Y
  | quux : (nat -> foo X Y) -> foo X Y.

Check foo_ind.

Inductive foo' (X:Type) : Type :=   
  | C1 : list X → foo' X → foo' X   
  | C2 : foo' X. 

Check foo'_ind.

Definition plus_assoc_fun : nat -> Prop :=
  fun n => forall m p, n + (m + p) = (n + m) + p.

Lemma plus_assoc' : forall n, plus_assoc_fun n.
Proof.
  induction n.
  - unfold plus_assoc_fun. simpl. auto.
  - unfold plus_assoc_fun in *. simpl.
    intros.
    rewrite <- IHn. auto.
Qed.

Definition plus_comm_fun : nat -> Prop := 
  fun m => forall n, n + m = m + n.

Lemma plus_comm' : forall m, plus_comm_fun m.
Proof.
  induction m.
  - unfold plus_comm_fun. simpl. intros. rewrite <- plus_n_O. auto.
  - unfold plus_comm_fun in *. simpl. intros. rewrite <- IHm. rewrite plus_n_Sm. auto.
Qed.

