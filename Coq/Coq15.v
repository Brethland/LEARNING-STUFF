(*
  This is exercises for <Software Foundations> CH8.
  Author : Brethland, Late 2019.
*)

Require Import Coq.Arith.Arith. 
Require Import Coq.Bool.Bool. 
Require Export Coq.Strings.String. 
Require Import Coq.Logic.FunctionalExtensionality. 
Require Import Coq.Lists.List.
Require Import Unicode.Utf8.
Require Import Setoid.

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

Theorem false_beq_string : ∀ x y : string, x ≠ y → beq_string x y = false. 
Proof. 
  intros x y. rewrite beq_string_false_iff. 
  intros H. apply H. 
Qed.

Definition total_map (A:Type) := string → A.

Definition t_empty {A:Type} (v : A) : total_map A :=   (fun _ => v).

Definition t_update {A:Type} (m : total_map A) (x : string) (v : A) := 
  fun x' => if beq_string x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Axiom functional_extensionality : ∀ {X Y: Type} {f g : X → Y}, (∀ (x:X), f x = g x) → f = g.

Lemma t_apply_empty: ∀ (A:Type) (x: string) (v: A), (_ !-> v) x = v.
Proof.
  intros.
  unfold t_empty. auto.
Qed.

Lemma t_update_eq : ∀(A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update. rewrite <- beq_string_refl.
  auto.
Qed.

Theorem t_update_neq : ∀(A : Type) (m : total_map A) x1 x2 v,
    x1 ≠ x2 →
    (x1 !-> v ; m) x2 = m x2.
Proof.
  intros.
  unfold t_update. apply beq_string_false_iff in H.
  rewrite H. auto.
Qed.

Lemma t_update_shadow : ∀(A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros.
  apply functional_extensionality.
  intros. unfold t_update.
  destruct (beq_string x x0) eqn:HE.
  - auto.
  - auto.
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

Theorem t_update_permute : ∀(A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
    x2 ≠ x1 →
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros.
  apply functional_extensionality.
  intros. unfold t_update.
  destruct (beq_stringP x1 x).
  - destruct (beq_stringP x2 x).
    + rewrite e,e0 in H. unfold not in H.
      destruct H. auto.
    + auto.
  - destruct (beq_stringP x2 x).
    + auto.
    + auto.
Qed.

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
 