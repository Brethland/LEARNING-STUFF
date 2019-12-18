Require Import List Arith Nat.
Import ListNotations.
From Coq Require Import Unicode.Utf8.

Inductive Subseq : list nat -> list nat -> Prop :=
| Subseq_nil : Subseq [] []
| Subseq_take : forall a xs ys, Subseq xs ys -> Subseq (a :: xs) (a :: ys)
| Subseq_drop : forall a xs ys, Subseq xs ys -> Subseq xs (a :: ys).

Fixpoint subseq_match (xs ys : list nat) : bool :=
  match xs with
  | [] => true
  | x :: xs' =>
    (fix go (us : list nat) :=
      match us with
      | [] => false
      | u :: us' =>
          if x =? u
          then subseq_match xs' us'
          else go us'
      end) ys
  end. 

Lemma silly1 : forall xs, Subseq [] xs.
Proof.
  induction xs. constructor. constructor. auto.
Qed.

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

Lemma silly2: forall a xs ys,
    subseq_match xs ys = true -> subseq_match xs (a::ys) = true.
Proof.
  intros.
  generalize dependent a. generalize dependent ys.
  induction xs; intros; auto.
  simpl in *. rewrite H.
  destruct (a =? a0) eqn:Ha0; auto.
  destruct (beq_natP a a0). subst.
  induction ys.
  discriminate H.
  destruct (a0 =? a) eqn: Haa10; auto.
  inversion Ha0.
Qed.

Lemma silly3: forall a xs ys,
    subseq_match xs ys = true -> subseq_match (a::xs) (a::ys) = true.
Proof.
  intros. simpl. destruct (beq_natP a a). auto. exfalso. apply H0. auto. Qed.

Theorem subseq_match_correct : forall (xs ys : list nat),
  subseq_match xs ys = true <-> Subseq xs ys.
Proof.
  split.
  - intros. generalize dependent xs. induction ys;intros.
    destruct xs. constructor. inversion H. destruct xs.
    apply silly1. destruct (n =? a) eqn:Heq.
    + simpl in H. rewrite Heq in H.
      destruct (beq_natP n a). rewrite H0. constructor. apply IHys. auto.
      inversion Heq.
    + simpl in H. rewrite Heq in H. constructor. apply IHys. auto.
  - intros. induction H; auto.
    apply silly3. auto.
    apply silly2. auto.
Qed. 