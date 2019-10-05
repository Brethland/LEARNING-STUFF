(*
  Exercises for <Software Foundations> CH7.
  Author : Brethland, Late 2019.
*)

From Coq Require Import Nat.
From Coq Require Import Unicode.Utf8.
Require Import Setoid.
Require Import PeanoNat.
Require Import Peano.
Require Import Arith.
Require Import List.

Inductive reflect (P : Prop) : bool → Prop := 
  | ReflectT : P → reflect P true 
  | ReflectF : ¬ P → reflect P false.

Theorem iff_reflect : ∀ P b, (P ↔ b = true) → reflect P b. 
Proof. 
  intros P b H. destruct b.   
  - apply ReflectT. rewrite H. reflexivity.   
  - apply ReflectF. rewrite H. intros H'. inversion H'. 
Qed.

Theorem reflect_iff : ∀ P b, reflect P b → (P ↔ b = true). 
Proof.
  intros. split.
  - destruct H.
    + auto.
    + intros. unfold not in H. apply H in H0. inversion H0.
  - destruct H.
    + auto.
    + intros. inversion H0.
Qed.

Lemma beq_natP : ∀ n m, reflect (n = m) (beq_nat n m). 
Proof.   
  intros n m. apply iff_reflect. rewrite beq_nat_true_iff. reflexivity. 
Qed.

Notation "x :: l" := (cons x l)
                      (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Fixpoint count n l :=   
  match l with   
  | [] => 0   
  | m :: l' => (if beq_nat n m then 1 else 0) + count n l'   
  end.

Theorem beq_natP_practice : ∀ n l,   count n l = 0 → ~(In n l). 
Proof.
  intros n l. induction l.
  - intros. unfold not. intros. inversion H0.
  - simpl. intros. destruct (beq_natP n a) as [H1 | H1].
    + inversion H.
    + unfold not.
      intros. destruct H0.
      ++ destruct H1. auto.
      ++ apply IHl in H. destruct H. auto.
Qed.

Inductive nostutter {X:Type} : list X → Prop := 
  | EmptyStutter : nostutter []
  | Onestutter : forall (a : X), nostutter [a]
  | ConsStutter : forall (a b: X) (l : list X), nostutter (b :: l) -> a <> b -> nostutter (a :: b :: l).

Example test_nostutter_4: not (nostutter [3;1;1;4]). 
Proof.
  Proof. intro.   
  repeat match goal with     
         h: nostutter _ |- _ => inversion h; clear h; subst   
         end.   
  contradiction H5; 
  auto.
Qed.

Lemma cons_inj : forall {X} (a : X) (l1 l2 : list X), l1 = l2 -> a :: l1 = a :: l2.
Proof.
  intros. rewrite H. auto.
Qed.

Inductive in_order_merge {X : Type} : list X -> list X -> list X -> Prop :=
  | EmptyMerge : in_order_merge [] [] []
  | ConsMergeL : forall (a : X) (l l1 l2 : list X), in_order_merge l l1 l2
                                                  -> in_order_merge (a :: l) (a :: l1) l2
  | ConsMergeR : forall (a : X) (l l1 l2 : list X), in_order_merge l l1 l2
                                                  -> in_order_merge (a :: l) l1 (a :: l2).

Lemma filter_correct : forall {X} (l l1 l2 : list X) (test: X -> bool),
  in_order_merge l l1 l2 -> (forall x : X, In x l1 -> test x = true)
  -> (forall x : X, In x l2 -> test x = false) -> filter test l = l1.
Proof.
  intros X l. induction l.
  - intros. inversion H. auto.
  - intros. inversion H.
    + assert(H' : In a l1).
      rewrite <- H3. simpl. left. auto.
      apply H0 in H'. simpl. rewrite H'.
      apply cons_inj. apply IHl with (l2:=l4).
      rewrite <- H5 in H6. auto. intros.
      assert(H'' : In x l1).
      rewrite <- H3. simpl. right. auto.
      apply H0 in H''. auto. rewrite <- H5 in H1. auto.
    + assert(H' : In a l2).
      rewrite <- H5. simpl. left. auto.
      apply H1 in H'. simpl. rewrite H'.
      apply IHl with (l2:=l4).
      auto. auto. intros.
      assert(H'' : In x l2).
      rewrite <- H5. simpl. right. auto.
      apply H1 in H''. auto.
Qed.

Inductive pal {X : Type} : list X -> Prop :=
  | EmptyPal : pal []
  | SinglePal : forall (a : X), pal [a]
  | ConsPal : forall (a : X) (l : list X), pal l -> pal ([a] ++ l ++ [a]).

Lemma silly : forall {X} (a : X) (l : list X), a :: l = [a] ++ l.
Proof.
  intros. simpl. auto.
Qed.

Lemma silly2 : forall {X} (a: X) (l1 l2: list X), 
  l1 = l2 -> l1 ++ [a] = l2 ++ [a].
Proof.
  intros. rewrite <- H. simpl. auto.
Qed.

Lemma rev_app : forall {X} (l1 l2 : list X), rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. generalize dependent l2.
  induction l1.
  - intros. simpl. rewrite app_nil_r. auto.
  - intros. simpl. rewrite app_assoc. apply silly2. auto.
Qed.

Lemma rev_single : forall {X} (a : X) (l : list X), l = rev l -> a :: l = rev(l ++ [a]).
Proof.
  intros. induction l.
  - simpl. auto.
  - rewrite rev_app. rewrite <- H. simpl. auto.
Qed.

Lemma pal_app_rev : forall {X} (l : list X), pal (l ++ rev l).
Proof.
  intros.
  induction l.
  - simpl. apply EmptyPal.
  - simpl. rewrite silly. rewrite (app_assoc l (rev l) [a]).
    apply ConsPal. auto.
Qed.

Lemma pal_rev : forall {X} (l : list X), pal l -> l = rev l.
Proof.
  intros.
  induction H.
  - simpl. auto.
  - simpl. auto.
  - simpl. assert(H' : a :: l = rev (l ++ [a]) -> a :: l ++ [a] = rev (l ++ [a]) ++ [a]).
    intros.  rewrite <- H0. auto.
    apply H'. apply rev_single. auto.
Qed.

Inductive disjoint {X : Type} : list X -> list X -> Prop :=
  | EmptyJoin : disjoint [] []
  | ConsJoinL : forall (a : X) (l1 l2 : list X), disjoint l1 l2 -> ~(In a l2) -> disjoint (a :: l1) l2
  | ConsJoinR : forall (a : X) (l1 l2 : list X), disjoint l1 l2 -> ~(In a l1) -> disjoint l1 (a :: l2).

Inductive noDup {X : Type} : list X -> Prop :=
  | EmptyDup : noDup []
  | ConsDup : forall (a : X) (l : list X), noDup l -> ~(In a l) -> noDup (a :: l).

Lemma not_in_cons : forall {X} (a a0 : X) (l : list X), ~In a (a0 :: l) -> a <> a0 /\ ~In a l.
Proof.
  intros. unfold not in H. split.
  - unfold not. intros. induction l.
    + simpl in H. destruct H. left. auto.
    + apply H. simpl. left. auto.
  - induction l.
    + simpl. auto.
    + simpl. unfold not. intros.
      destruct H0.
      ++ apply H. simpl. right. left. auto.
      ++ apply H. simpl. right. right. auto.
Qed.

Lemma disjoint_cons : forall {X} (a : X) (l1 l2 : list X), disjoint (a :: l1) l2 -> disjoint l1 l2.
Proof.
  intros.
  generalize dependent l1. induction l2.
  - intros. inversion H. auto.
  - intros. inversion H. auto.
    inversion H3.
    + apply ConsJoinR. apply IHl2. auto.
      apply not_in_cons in H4. destruct H4. auto.
    + rewrite H8. apply ConsJoinR. apply IHl2. auto.
      apply not_in_cons in H4. destruct H4. auto.
Qed.

Lemma disjoint_cons' : forall {X} (a : X) (l1 l2 : list X), disjoint l1 (a :: l2) -> disjoint l1 l2.
Proof.
  intros.
  generalize dependent l2. induction l1.
  - intros. inversion H. auto.
  - intros. inversion H. auto.
    inversion H2.
    + apply ConsJoinL. rewrite H7. apply IHl1. auto.
      apply not_in_cons in H4. destruct H4. auto.
    + apply ConsJoinL. apply IHl1. auto. 
      apply not_in_cons in H4. destruct H4. auto.
    + auto.
Qed.

Lemma disjoint_not : forall {X} (a : X) (l1 l2 : list X), disjoint (a :: l1) l2 -> ~In a l2.
Proof.
  intros.
  generalize dependent l1. induction l2.
  - intros. simpl. auto.
  - intros. simpl. unfold not. intros.
    destruct H0. 
    + rewrite H0 in H. inversion H. simpl in H5. apply H5. left. auto.
      simpl in H5. apply H5. left. auto.
    + unfold not in IHl2. apply IHl2 with (l1:=l1).
      ++ apply disjoint_cons' in H. auto.
      ++ auto.
Qed. 

Lemma In_app_iff : forall X l1 l2 (x : X),
  In x (l1 ++ l2) <-> In x l1 \/ In x l2.
Proof.
  intros.
  split.
  induction l1.
  - intros. simpl in H. right. auto.
  - simpl. intros [HA | HB].
    + left. left. auto.
    + apply IHl1 in HB.
      destruct HB.
      ++ left. right. auto.
      ++ right. auto.
  - apply in_or_app.
Qed.

Lemma noDup_app : forall {X} (l1 l2 : list X), noDup l1 -> noDup l2 -> disjoint l1 l2 -> noDup (l1 ++ l2).
Proof.
  intros.
  generalize dependent l2.
  induction l1.
  - intros. simpl. auto.
  - intros. simpl. apply ConsDup. apply IHl1.
    + inversion H. auto.
    + auto.
    + apply disjoint_cons in H1. auto.
    + unfold not. intros. apply In_app_iff in H2. destruct H2.
      ++ inversion H. apply H6 in H2. auto.
      ++ apply disjoint_not in H1. apply H1 in H2. auto.
Qed.

Lemma so_silly : forall {X} (a : X) (l1 l2 : list X), l1 = l2 -> a :: l1 = a :: l2.
Proof.
  intros. rewrite H. auto.
Qed.

Lemma in_split : ∀ (X:Type) (x:X) (l:list X), In x l → ∃ l1 l2, l = l1 ++ x :: l2.
Proof.
  intros.
  induction l.
  - inversion H.
  - simpl in H. destruct H.
    + rewrite H. exists [], l. auto.
    + apply IHl in H. destruct H as [l1 [l2 HA]].
      exists (a :: l1), l2.
      simpl. apply so_silly. auto.
Qed.

Inductive repeats {X:Type} : list X -> Prop :=
  | repeat_join : forall l1 l2, (exists x, In x l1 /\ In x l2) -> repeats (l1 ++ l2).

Definition excluded_middle := forall (P : Prop), P \/ (~ P).

Theorem pigeonhole_principle: ∀ (X:Type) (l1 l2:list X),   
  excluded_middle → 
   (∀ x, In x l1 → In x l2) → 
  length l2 < length l1 → repeats l1.
Proof.
  intros X l1. induction l1 as [|x l1' IHl1']. 
  - intros. inversion H1.
  - intros. rewrite silly. apply repeat_join.
    exists x. split. simpl. left. auto.
    simpl in H0. Abort.
 
(* Leaving filter_challenge2 palidome_converse pigeonhole_principle *)