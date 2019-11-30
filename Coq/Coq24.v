(*
  Exercises for <Software Foundations> V2 CH2.
  Arthur : Brethland, Late 2019.
 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
Add LoadPath "C:\Users\ycy12\Documents\Workspace\LEARNING-STUFF\Coq".
Load Coq19.

Definition Assertion := state -> Prop.
Definition assert_implies (P Q : Assertion) : Prop :=
  ∀st, P st → Q st.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q ∧ Q ->> P) (at level 80) : hoare_spec_scope.

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  ∀st st',
     st =[ c ]⇒ st' →
     P st →
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_post_true : ∀(P Q : Assertion) c,
  (∀st, Q st) →
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H. Qed.

Theorem hoare_pre_false : ∀(P Q : Assertion) c,
  (∀st, ¬(P st)) →
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP. Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).
Notation "P [ X ⊢> a ]" := (assn_sub X a P)
                             (at level 10, X at next level).

Theorem hoare_asgn : ∀Q X a,
  {{Q [X ⊢> a]}} X ::= a {{Q}}.
Proof.
  intros Q X a.
  unfold assn_sub. unfold hoare_triple.
  intros. inversion H;subst. apply H0.
Qed.

Lemma assn_sub_ex1 : {{(fun st => st X <= 10) [X ⊢> 2 * X] }}
                       X ::= 2 * X
                     {{fun st => st X <= 10}}.
Proof.
  apply hoare_asgn.
Qed.

Lemma assn_sub_ex2 : {{(fun st => st X >= 0 /\ st X <= 5) [X ⊢> 3]}}
                       X ::= 3
                     {{fun st => st X >= 0 /\ st X <= 5}}.
Proof.
  apply hoare_asgn.
Qed.
Axiom functional_extensionality : ∀ {X Y: Type} {f g : X → Y}, (∀ (x:X), f x = g x) → f = g.

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

Theorem hoare_asgn_fwd :
  ∀m a P,
  {{fun st => P st ∧ st X = m}}
    X ::= a
  {{fun st => P (X !-> m ; st)
           ∧ st X = aeval (X !-> m ; st) a }}.
Proof.
  intros. unfold hoare_triple. intros.
  inversion H. subst. destruct H0.
  subst. rewrite t_update_shadow. rewrite t_update_same. split.
  - auto.
  - rewrite t_update_eq. auto.
Qed.

Theorem hoare_asgn_fwd_exists :
  ∀a P,
  {{fun st => P st}}
    X ::= a
  {{fun st => ∃m, P (X !-> m ; st) ∧
                st X = aeval (X !-> m ; st) a }}.
Proof.
  intros a P.
  unfold hoare_triple. intros.
  inversion H;subst. exists (st X).
  rewrite t_update_shadow. rewrite t_update_same. split.
  auto. rewrite t_update_eq. auto.
Qed.

