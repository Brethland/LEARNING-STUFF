(*
  Exercises for <Software Foundations> CH6.
  Author : Brethland, Late 2019.
*)

From Coq Require Import Peano.
From Coq Require Import Nat.
From Coq Require Import Arith.
From Coq Require Import List.

Lemma and_intro : forall (A B : Prop),
  A -> B -> and A B.
Proof.
  intros.
  split.
  apply H.
  apply H0.
Qed.

Example and_exercise : forall (n m : nat),
  n + m = 0 -> and (n = 0) (m = 0).
Proof.
  intros.
  apply and_intro.
  - induction n.
    + auto.
    + inversion H.
  - induction m.
    + auto.
    + rewrite plus_comm in H.
      inversion H.
Qed.

Lemma proj1 : forall (P Q : Prop),
  P /\ Q -> P.
Proof.
  intros.
  destruct H.
  auto.
Qed.

Lemma proj2 : forall (P Q : Prop),
  P /\ Q -> Q.
Proof.
  intros.
  destruct H.
  auto.
Qed.

Lemma and_commut : forall (P Q : Prop),
  P /\ Q -> Q /\ P.
Proof.
  intros.
  destruct H.
  split.
  auto.
  auto.
Qed.

Lemma and_assoc : forall (P Q R : Prop),
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  split.
  trivial. trivial. trivial.
Qed.

(* ex falso quodlibet *)

Fact not_implies_our_not : forall (P : Prop),
  ~ P -> (forall (Q :Prop), P -> Q).
Proof.
  intros.
  destruct H.
  auto.
Qed.

Theorem not_False :   ~ False. 
Proof.   
  unfold not. 
  intros H. 
  destruct H. 
Qed.

Lemma contradiction_implies_everything : forall (P Q : Prop),
  (P /\ ~ P) -> Q.
Proof.
  intros P Q [HA HNA].
  unfold not in HNA.
  apply HNA in HA.
  inversion HA.
Qed.

Lemma double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros.
  unfold not.
  intros.
  apply H0.
  auto.
Qed.

Lemma contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~ Q -> ~ P).
Proof.
  intros P Q H.
  unfold not.
  intros.
  apply H in H1.
  apply H0 in H1.
  inversion H1.
Qed.

Fact not_both_true_false : forall P : Prop,
  ~ (P /\ ~ P).
Proof.
  intros.
  unfold not.
  intros [HA HNA].
  apply HNA in HA.
  inversion HA.
Qed.

Theorem not_true_is_false : forall b : bool,   
  b <> true -> b = false. 
Proof. 
  intros [] H.
  - unfold not in H.
    exfalso.
    apply H.
    auto.
  - auto.
Qed.

Lemma True_is_true : True.
Proof.
  apply I.
Qed.

Lemma iff_sym : forall (P Q : Prop),
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  auto.
  auto.
Qed.

Lemma not_true_iff_false : forall b : bool,
  b <> true <-> b = false.
Proof.
  intros b.
  split.
  apply not_true_is_false.
  intros.
  rewrite H.
  intros H'.
  inversion H'.
Qed.

Lemma or_distriutes_over_and : forall (P Q R : Prop),
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [HR | [HQ HR]].
    + auto.
    + auto.
  - intros [[HP | HQ] [HP' | HR]].
    + auto.
    + auto.
    + auto.
    + auto.
Qed.

Require Import Coq.Setoids.Setoid.

Lemma mult_0 : forall (n m : nat),
  n * m = 0 <-> n = 0 \/ m = 0.
Admitted.

Lemma mult_0_3 : forall (n m p : nat),
  n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros.
  rewrite 2 mult_0.
  rewrite or_assoc.
  reflexivity.
Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2.
  auto.
Qed.

Lemma exists_example : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  auto.
Qed.

Lemma dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros.
  unfold not.
  intros.
  destruct H0 as [x E].
  apply E in H.
  inversion H.
Qed.

Lemma dist_exists_or : forall (X : Prop) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split.
  - intros [x0 [HP | HQ]].
    left. exists x0. auto.
    right. exists x0. auto.
  - intros [[x1 E1] | [x2 E2]].
    exists x1. left. auto.
    exists x2. right. auto.
Qed.

(* Fixpoint In {X : Type} (x : X) (l : list X) :=
  match l with
  | nil => False
  | cons e es => x = e \/ In x es
  end. *)

Notation "x :: y" := (cons x y)
                    (at level 60, right associativity).
Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                    (at level 60, right associativity).

Example In_example :  forall n, In n [2;4] -> exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. auto.
  - exists 2. auto.
Qed.

Lemma In_map : forall (X Y : Type) (f : X -> Y) (l : list X) (x : X),
  In x l -> In (f x) (map f l).
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    destruct H.
    + rewrite <- H. left. auto.
    + apply IHl in H.
      right. apply H.
Qed.

Lemma In_map_iff : forall (X Y : Type) (f : X -> Y) (l : list X) (y : Y),
  In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros. split.
  induction l.
  - simpl. intros. inversion H.
  - simpl. intros [HA | HB].
    + exists a. split. auto. left. auto.
    + apply IHl in HB. destruct HB. exists x.
      split. destruct H. auto. right. destruct H. auto.
  - intros [x [HA HB]].
    rewrite <- HA. apply In_map. auto.
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
    + apply IHl1 in HB. (* or_assoc *)
      destruct HB.
      ++ left. right. auto.
      ++ right. auto.
  - apply in_or_app.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) :=
  match l with
  | [] => True
  | e :: es => P e /\ All P es
  end.

Lemma or_forall : forall {X : Type} (P1 P2 : Prop),
  (forall x : X, P1) \/ (forall x : X, P2) -> (forall x : X, P1 \/ P2).
Proof.
  intros.
  destruct H.
  auto. auto.
Qed.

Lemma All_In : forall T (P : T -> Prop) (l : list T),
  (forall x : T, In x l -> P x) <-> All P l.
Proof.
  intros. split.
  - induction l.
    + intros.
      unfold All. auto.
    + intros. simpl. split. 
      ++ apply H. simpl. left. auto.
      ++ apply IHl. simpl in H.
         intros. apply H.
         right. auto.
  - induction l.
    + intros. inversion H0.
    + intros.
      destruct H.
      destruct H0 as [HA | HB].
      ++ rewrite <- HA. auto.
      ++ apply IHl. auto. auto.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) :=
  fun n => if odd n then Podd n else Peven n.

Require Import Unicode.Utf8.

Theorem combine_odd_even_intro :   ∀ (Podd Peven : nat → Prop) (n : nat),
  (odd n = true → Podd n) →
  (odd n = false → Peven n) →
  combine_odd_even Podd Peven n.
Proof.
  intros.
  unfold combine_odd_even.
  destruct (odd n).
  - apply H. auto.
  - apply H0. auto.
Qed.

Theorem combine_odd_even_elim_odd :
   ∀ (Podd Peven : nat → Prop) (n : nat),
  combine_odd_even Podd Peven n →
  odd n = true → 
  Podd n.
Proof.
  intros.
  unfold combine_odd_even in H.
  rewrite H0 in H. auto.
Qed.

Theorem combine_odd_even_elim_even :
  ∀ (Podd Peven : nat → Prop) (n : nat),
  combine_odd_even Podd Peven n →
  odd n = false →
  Peven n. 
Proof.
(*   Too trivial.*)
Admitted.

Axiom functional_extensionality : ∀ {X Y: Type} {f g : X → Y}, 
  (∀ (x:X), f x = g x) → f = g.

Example function_equality_ex2 :   (fun x => plus x 1) = (fun x => plus 1 x). 
Proof.   
  apply functional_extensionality. 
  intros x.   
  apply plus_comm. 
Qed.

Print Assumptions All_In.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=   
  match l1 with   
  | [] => l2   
  | x :: l1' => rev_append l1' (x :: l2)   
  end. 

Definition tr_rev {X} (l : list X) : list X :=   
  rev_append l [].

Lemma rev_append_app: forall {X : Type} (l l1 l2: list X),
    rev_append l (l1 ++ l2) = rev_append l l1 ++ l2.
  intros.
  generalize dependent l2.
  generalize dependent l1.
  induction l as [| h t IH].
  - auto.
  - intros. simpl.
    apply (IH (h::l1)).
Qed.

Lemma tr_rev_app : forall {X : Type} (l l1 : list X),
  rev_append l l1 = tr_rev l ++ l1.
Proof.
  intros. generalize dependent l1. unfold tr_rev.
  induction l.
  - auto.
  - simpl. intros.
    rewrite <- (@rev_append_app X l [a] l1).
    auto.
Qed.

Theorem app_silly : forall X (l1 l2 l : list X),
  l1 = l2 -> l1 ++ l = l2 ++ l.
Proof.
  intros.
  rewrite H.
  auto.
Qed.

Check functional_extensionality.

Check f_equal.

Lemma tr_rev_correct : ∀ X, @tr_rev X = @rev X. 
Proof.
  intros.
  apply functional_extensionality.
  intros. 
  induction x.
  - auto.
  - simpl. unfold tr_rev. simpl.
    rewrite tr_rev_app.
    apply (@app_silly X (tr_rev x) (rev x) [a]).
    auto.
Qed.

Fixpoint evenb (n : nat) :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S n') => evenb n'
  end.

Lemma neg_id : forall b : bool, negb (negb b) = b.
Proof.
  intros [].
  - auto.
  - auto.
Qed.

Lemma evenb_S: forall n : nat, evenb (S n) = negb (evenb n).
Proof.
  intros n.
  induction n.
  - auto.
  - rewrite -> IHn.
    rewrite -> neg_id.
    auto.
Qed.


Theorem evenb_double_conv : ∀ n, ∃ k, n = if evenb n then double k else S (double k). 
Proof.
  intros.
  induction n.
  - exists 0. auto.
  - destruct IHn.
    destruct (evenb n) eqn:HA.
    + rewrite evenb_S. rewrite HA. simpl.
      exists x. auto.
    + rewrite evenb_S. rewrite HA. simpl.
      exists (S x). rewrite H. unfold double. simpl.
      rewrite plus_n_Sm. auto.
Qed.

Lemma andb_true_iff : ∀ b1 b2:bool, andb b1 b2 = true ↔ b1 = true ∧ b2 = true.
Proof. 
  intros. split.
  - intros.
    destruct b1. 
    + simpl in H. auto.
    + inversion H.
  - intros [HA HB].
    rewrite HA. rewrite HB. auto.
Qed.

Lemma orb_true_iff : ∀ b1 b2,  (b1 || b2)%bool = true ↔ b1 = true ∨ b2 = true.
Proof.
  intros.
  split.
  - intros.
    destruct b1.
    + left. auto.
    + simpl in H. right. auto.
  - intros [HA | HB].
    + rewrite HA. auto.
    + rewrite HB.
      destruct b1. auto. auto.
Qed. 

Theorem beq_nat_true_iff : ∀ n1 n2 : nat,   beq_nat n1 n2 = true ↔ n1 = n2. 
Proof.   
  intros n1 n2. split.   
  - apply beq_nat_true.   
  - intros H. rewrite H. rewrite <- beq_nat_refl. 
    reflexivity. 
Qed. 

Theorem beq_nat_false_iff : ∀ x y : nat,   beq_nat x y = false ↔ x ≠ y. 
Proof.
  intros. split.
  - intros.
    unfold not. intros. apply beq_nat_true_iff in H0.
    rewrite H0 in H. inversion H.
  - generalize (beq_nat_true_iff x y).
    destruct beq_nat.
    + intros. destruct H0. apply H. auto.
    + intros. auto.
Qed.

Fixpoint beq_list {A : Type} (beq : A -> A -> bool) (l1 l2 : list A) :=
  match l1,l2 with
  | [] , y :: et => false
  | x :: es , [] => false
  | []      , [] => true
  | x :: es , y :: et => andb (beq x y) (beq_list beq es et)
  end.


Lemma beq_list_true_iff :   ∀ A (beq : A → A → bool),     
  (∀ a1 a2, beq a1 a2 = true ↔ a1 = a2) →     
  ∀ l1 l2, beq_list beq l1 l2 = true ↔ l1 = l2. 
Proof.
  intros.
  split.
  - intros.
    generalize dependent l2.
    induction l1.
    + intros. destruct l2. auto. inversion H0.
    + intros. destruct l2.
      ++ inversion H0.
      ++ simpl in H0. apply andb_true_iff in H0. destruct H0.
         apply H in H0. rewrite H0. apply IHl1 in H1. rewrite H1. auto.
  - intros. generalize dependent l2. induction l1.
    + intros. destruct l2. auto. inversion H0.
    + intros. destruct l2.
      ++ inversion H0.
      ++ simpl. apply andb_true_iff. split.
         inversion H0. apply H. auto.
         apply IHl1. inversion H0. auto.
Qed.

Theorem forallb_true_iff : ∀ X test (l : list X),    forallb test l = true ↔ All (fun x => test x = true) l.
Proof.
  intros. split.
  - intros. induction l.
    + simpl. auto.
    + simpl. split.
      simpl in H. apply andb_true_iff in H. destruct H. auto.
      apply IHl. simpl in H. apply andb_true_iff in H. destruct H. auto.
  - intros. induction l.
    + simpl. auto.
    + simpl. apply andb_true_iff. split.
      simpl in H. destruct H. auto.
      simpl in H. destruct H. apply IHl in H0. auto.
Qed.

Theorem excluded_middle_irrefutable: ∀ (P:Prop),   ¬ ¬ (P ∨ ¬ P). 
Proof.
  intros.
  unfold not. intros. apply H.
  right. intros. apply H. left. auto.
Qed.

Theorem not_exists_dist :
  (forall (P : Prop), P \/ (~ P)) ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros.
  destruct (H (P x)).
  + auto.
  + exfalso. apply H0. exists x. auto.
Qed.

Definition peirce := ∀ P Q: Prop,   ((P→Q)→P)→P. 
Definition double_negation_elimination := ∀ P:Prop,   ~~P → P. 
Definition de_morgan_not_and_not := ∀ P Q:Prop,   ~(~P ∧ ¬Q) → P∨Q. 
Definition implies_to_or := ∀ P Q:Prop,   (P→Q) → (¬P∨Q).
Definition excluded_middle := forall (P : Prop), P \/ (~ P).

Lemma double_negation_excluded_middle_iff : 
  excluded_middle <-> double_negation_elimination.
Proof.
  split.
  - intros. unfold excluded_middle in H.
    unfold double_negation_elimination.
    unfold not. intros.
    unfold not in H.
    elim H0. intros.
    apply H0. 