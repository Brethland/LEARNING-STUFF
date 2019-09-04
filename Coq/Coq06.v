(*
  Some exercises come from Software Foundations Book1 CH2.
  Author : Brethland.
*)

Module NatPlayground.
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n: nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

(* Compute (plus 5 4). *)

Fixpoint multiply (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (multiply n' m)
  end.

Compute (multiply 6 7).

Example test_mult1 : (mult 3 3) = 9.
Proof.
  simpl. reflexivity. Qed.

Fixpoint factorial (n : nat) :nat :=
  match n with
  | O => S O
  | S O => S O
  | S n' => multiply n (factorial n')
  end.

Compute (factorial 5).

Example test_lemma: (factorial 5) = (multiply 10 12).
Proof. reflexivity. Qed.

Fixpoint beq_n(n m : nat) :bool :=
  match n , m with
  | O , O => true
  | S n' ,  O => false
  | O , S m' => false
  | S n' , S m' => beq_n n' m'
  end.

Compute (beq_n 5 5).

Fixpoint leq_n(n m : nat) :bool :=
  match n , m with
  | O , _ => true
  | S n' , O => false
  | S n' , S m' => leq_n n' m'
  end.

Definition lts_n (n m : nat) :bool :=
 andb (leq_n n m) (negb (beq_n n m)).

Compute (lts_n 6 7).

Lemma plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Lemma plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity. Qed.

Lemma mult_O_l : forall n : nat, O * n = O.
Proof.
  intros n. simpl. reflexivity. Qed.

Lemma plus_id : forall n m : nat, n = m ->
  n + n = m + m.
Proof.
  intros n m. 
  intros H. 
  rewrite <- H. 
  simpl. 
  reflexivity.
Qed.

Lemma plus_id_3: forall n m o : nat, n = m -> m = o ->
  n + m = m + o.
Proof.
  intros n m o.
  intros H.
  rewrite -> H.
  intros I.
  rewrite -> I.
  simpl.
  reflexivity.
Qed.

Lemma mult_S_l: forall n m :nat, m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_l. 
  rewrite -> H.
  reflexivity.
Qed.

Lemma mult_0_r: forall n : nat, n * 0 = 0.
Proof.
  intros n.
  induction n.
  - auto.
  - simpl. auto.
Qed.

Lemma plus_n_Sm: forall n m : nat, S (n + m) = n + S m.
Proof.
  intros n m.
  induction n.
  - simpl. auto.
  - simpl. rewrite <- IHn. auto.
Qed.

Lemma plus_comm: forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction m.
  - auto.
  - simpl.
    rewrite <- plus_n_Sm.
    rewrite <- IHm.
    auto.
Qed.

Lemma plus_assoc : forall n m p :nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  - auto.
  - simpl. rewrite -> IHn. auto.
Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n')) 
  end.

Lemma double_plus : forall n : nat, double n = n + n.
Proof.
  intros n.
  induction n.
  - auto.
  - simpl. rewrite -> IHn. simpl. auto.
Qed.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
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

Lemma evenb_S_r : forall n : nat, evenb n = negb (evenb (S n)).
Proof.
  intros n.
  induction n.
  - auto.
  - simpl. 
    rewrite -> IHn.
    rewrite -> neg_id.
    auto.
Qed.

Lemma eqb_true : forall n m, beq_n n m = true -> n = m.
Proof.
  intros n.
  induction n.
  - intros.
    destruct m.
    + auto.
    + inversion H.
  - intros.
    destruct m.
    + inversion H.
    + apply f_equal.
      apply IHn.
      apply H.
Qed.

Check f_equal. (* Agda: cong *)

