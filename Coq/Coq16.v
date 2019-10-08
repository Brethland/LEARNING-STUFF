(*
  This is exercises for <Software Foundations> CH9.
  Author : Brethland, Late 2019.
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

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_ss : forall n : nat, ev n -> ev (S (S n)).

Check (ev_ss 2 (ev_ss 0 ev_0)).

Theorem ev_4'' : ev 4. Proof.   Show Proof.   apply ev_ss. 
  Show Proof.   apply ev_ss.   Show Proof.   apply ev_0.   Show Proof. Qed.

Theorem ev_8 : ev 8. 
Proof.
  apply ev_ss. apply ev_ss. apply ev_ss. apply ev_ss. apply ev_0. Qed.

Definition ev_8' := ev_ss 6 (ev_ss 4 (ev_ss 2 (ev_ss 0 ev_0))).

Definition add1 : nat → nat. intro n. Show Proof. apply S. Show Proof. apply n. Defined.

Print add1.
Compute add1 2.

Definition add1' := fun n => S n.
Print add1'.

Module Props.

Module And.

Inductive and (P Q : Prop) : Prop :=
| conj : P → Q → and P Q.

End And.

Definition and_comm'_aux P Q (H : P ∧ Q) : Q ∧ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P ∧ Q ↔ Q ∧ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

Print and_comm'.

Definition conj_fact P Q R : P ∧ Q → Q ∧ R → P ∧ R :=
  fun HPQ HQR => match HPQ with
                  | conj HP HQ => match HQR with
                                    | conj HQ' HR => conj HP HR
                                  end
                 end.

Module Or. 
Inductive or (P Q : Prop) : Prop := | or_introl : P → or P Q | or_intror : Q → or P Q.
End Or.

Definition or_comm : ∀ P Q, P ∨ Q → Q ∨ P :=
  fun P Q H => match H with
          | or_introl HP => or_intror HP
          | or_intror HQ => or_introl HQ
          end.

Module Ex. 

Inductive ex {A : Type} (P : A → Prop) : Prop := 
  | ex_intro : ∀ x : A, P x → ex P. 

End Ex.

Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 1 (ev_ss 0 ev_0).
End Props.

Module MyEquality. 

Inductive eq {X:Type} : X → X → Prop := 
| eq_refl : ∀ x, eq x x.

Notation "x = y" := (eq x y) (at level 70, no associativity) : type_scope.

End MyEquality.

Lemma equality__leibniz_equality : ∀ (X : Type) (x y: X),   x = y → ∀ P:X→Prop, P x → P y. 
Proof.
  intros.
  rewrite <- H.
  auto.
Qed.

Lemma leibniz_equality__equality : ∀ (X : Type) (x y: X),   (∀ P:X→Prop, P x → P y) → x = y. 
Proof.
  intros.
  apply (H (fun y => x = y)). auto.
Qed.