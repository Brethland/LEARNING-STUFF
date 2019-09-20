(*
  Exercise for <Software Foundations> CH5.
  Author : Brethland.
*)

From Coq Require Import Nat.
From Coq Require Import Arith.
From Coq Require Import Peano.
From Coq Require Import List.

Lemma silly_ex : (forall n : nat, even n = true -> odd (S n) = true) ->
                 odd 3 = true -> even 4 = true.
Proof.
  intros.
  apply H0.
Qed.

Lemma apply_exercise : forall (l1 l2 : list nat),
  l1 = rev l2 -> l2 = rev l1.
Proof.
  intros.
  symmetry.
  rewrite -> H.
  apply rev_involutive.
Qed.

Lemma trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros.
  rewrite -> H.
  apply H0.
Qed.

Notation "x :: y" := (cons x y)                      
                    (at level 60, right associativity).
Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..). 
Notation "x ++ y" := (app x y)                      
                    (at level 60, right associativity).

Lemma trans_eq_example : forall (a b c d e f : nat),
  [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros.
  apply trans_eq with [c;d].
  apply H. apply H0.
Qed.

Definition minustwo (n : nat) :=
  minus n 2.

Lemma trans_eq_exercise : forall (n m o p: nat),
  m = minustwo o -> (n + p) = m -> (n + p) = minustwo o.
Proof.
  intros.
  apply trans_eq with m.
  apply H0. apply H.
Qed.

Lemma inversion_ex1 : forall (n m o : nat),
  [n;m] = [o;o] -> n = m.
Proof.
  intros.
  inversion H.
  auto.
Qed.

Example inversion_ex3: forall (X : Type) (x y z w : X) (l j : list X),
  x :: y :: l = w :: z :: j -> x :: l = z :: j -> x = y.
Proof.
  intros.
  inversion H0.
  inversion H.
  auto.
Qed.

Example inversion_ex6 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] -> y :: l = z :: j -> x = z.
Proof.
  intros.
  inversion H.
Qed.

Lemma S_injective : forall (n m :nat),
  S n = S m -> n = m.
Proof.
  intros.
  inversion H.
  auto.
Qed.

Lemma plus_n_n_injective : forall (n m : nat),
  n + n = m + m -> n = m.
Proof.
  intros n.
  induction n.
  - intros m H. destruct m.
    + auto.
    + inversion H.
  - intros m H. destruct m.
    + inversion H.  
    + inversion H.
      rewrite <- 2 plus_n_Sm in H1.
      inversion H1.
      apply IHn in H2.
      auto.
Qed.

Lemma beq_injective : forall (n m : nat),
  beq_nat n m = true -> n = m.
Proof.
  intros n.
  induction n.
  - intros m H. destruct m.
    + auto.
    + inversion H.
  - intros m H. destruct m.
    + inversion H.
    + inversion H.
      apply IHn in H1.
      auto.
Qed.

Lemma nth_error_after_last : forall (n : nat) (X : Type) (l : list X),
  length l = n -> nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l.
  - intros n H.
    simpl in H.
    unfold nth_error.
    rewrite <- H.
    auto.
  - intros n H.
    simpl in H.
    inversion H.
    simpl.
    apply IHl.
    auto.
Qed.

Check f_equal.

Lemma eq_remove_cons : forall (X:Type) (l1 l2: list X) (x: X),
  l1 = l2 -> x :: l1 = x :: l2.
  intros X l1 l2 x.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Lemma combine_split : forall (X Y : Type) (l : list (X * Y)) l1 l2,
  split l = (l1 , l2) -> combine l1 l2 = l.
Proof.
	intros X Y l.
	induction l as [| x y].
	- intros.
    inversion H.
    auto.
	- intros l1 l2.
		simpl.
		destruct x.
		destruct (split y).
		destruct l1.
		+ simpl.
			intros H.
      inversion H.
		+ induction l2.
			++ intros H.
         inversion H.
			++ intros H.
         inversion H.
				 simpl.
				 rewrite IHy. auto.
         rewrite H2 , H4.
         auto.
Qed.

Definition sillyfun1 (n : nat) : bool :=   
    if beq_nat n 3 then true   
    else if beq_nat n 5 then true   
    else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true -> odd n = true. 
Proof.   
  intros n eq. 
  unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  - apply beq_injective in Heqe3.
    rewrite -> Heqe3.
    auto.
  - destruct (beq_nat n 5) eqn:Heqe5.
    + apply beq_injective in Heqe5.
      rewrite -> Heqe5.
      auto.
    + inversion eq.
Qed.

Lemma siily_bool : forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros.
  destruct f eqn:Hf.
Abort.

Lemma S_beq_injective : forall (n m : nat),
  (S n =? S m) = (n =? m).
Proof.
  intros.
  auto.
Qed.

Lemma beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof. 
  intro.
  induction n.
  - destruct m.
    + auto.
    + auto.
  - destruct m.
    + auto.
    + rewrite 2 S_beq_injective.
      trivial.
Qed.

Lemma silly_beq: forall n : nat,
  beq_nat n n = true.
Proof.
  intros.
  induction n.
  - auto.
  - simpl.
    auto.
Qed.

Lemma beq_nat_trans : forall n m p,   
  beq_nat n m = true ->  
  beq_nat m p = true ->  
  beq_nat n p = true.
Proof.
  intros.
  apply beq_injective in H.
  apply beq_injective in H0.
  rewrite -> H.
  rewrite <- H0.
  apply silly_beq.
Qed.

Lemma split_combine : forall (X Y : Type) (l1 : list X) (l2 : list Y),
  length l1 = length l2 -> split (combine l1 l2) = (l1,l2).
Proof.
  intros X Y l1.
  induction l1.
  - intros.
    destruct l2.
    + auto.
    + inversion H.
  - intros.
    simpl.
    destruct l2.
    + inversion H.
    + inversion H.
      simpl.
      rewrite -> IHl1.
      auto.
      apply H1.
Qed.

Lemma filter_exercise : forall (X :Type) (test : X -> bool) (x : X) (l lf : list X),
  filter test l = x :: lf -> test x = true.
Proof.
  intros.
  induction l.
  - inversion H.
  - simpl in H.
    destruct (test a) eqn:Hea.
    + inversion H.
      rewrite <- H1.
      auto.
    + rewrite -> IHl.
      auto.
      auto.
Qed.

Fixpoint forallb {X : Type} (f : X -> bool) (l : list X) :=
  match l with
  | [] => true
  | x :: s => if f x then forallb f s
                    else false
  end.

Fixpoint existb {X : Type} (f : X -> bool) (l : list X) :=
  match l with
  | [] => false
  | x :: s => if f x then true
                    else existb f s
  end.

Definition compose {A B C : Type} (f : B -> C) (g : A -> B) :=
  fun x => f (g x).

Definition existb' {X : Type} (f : X -> bool) (l : list X) :=
   negb (forallb (compose negb f) l).

Lemma compose_neg : forall (X : Type) (f : X -> bool) (x : X),
  f x = true -> (compose negb f) x = false.
Proof.
  intros.
  unfold compose.
  rewrite -> H.
  auto.
Qed.

Lemma compose_neg' : forall (X : Type) (f : X -> bool) (x : X),
  f x = false -> (compose negb f) x = true.
Proof.
  intros.
  unfold compose.
  rewrite -> H.
  auto.
Qed.

Lemma existb_existb' : forall (X : Type) (f : X -> bool) (l : list X),
  existb f l = existb' f l.
Proof.
  intros.
  induction l.
  - auto. 
  - simpl.
    destruct (f a) eqn:Hea.
    + unfold existb'.
      simpl.
      apply compose_neg in Hea.
      rewrite -> Hea.
      auto.
    + unfold existb'.
      simpl.
      apply compose_neg' in Hea.
      rewrite -> Hea.
      rewrite -> IHl.
      auto.
Qed.