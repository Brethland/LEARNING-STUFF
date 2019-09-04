(*
  Some exercises come from Software Foundations Book1 CH1.
  Author : Brethland.
*)

Lemma andb_true_elim2: forall b c : bool, andb b c = true -> c = true.
Proof.
intros [].
- intros [].
  + intros H. rewrite <- H. reflexivity.
  + intros H. rewrite <- H. reflexivity.
- intros [].
  + intros H. rewrite <- H. reflexivity.
  + intros H. rewrite <- H. reflexivity.
Qed.

Fixpoint beq_n (n m : nat) : bool :=
  match n,m with
  | O, O => true
  | O , S m' => false
  | S n' , O => false
  | S n' , S m' => beq_n n' m'
  end. 

Lemma zero_nbeq_plus_1: forall n : nat, beq_n O (1 + n) = false.
Proof.
intros [|n'].
- reflexivity.
- reflexivity.
Qed.

Fixpoint nat_divmod(n m quo rem: nat) : nat * nat :=
  match n with
  | O => (quo, rem)
  | S n' => 
    match rem with
    | O => nat_divmod n' m (S quo) m
    | S rem' => nat_divmod n' m quo rem'
    end
  end.

Definition nat_div (a b :nat) :nat :=
  match b with
  | O => b
  | S b' => fst (nat_divmod a b' 0 b')
  end.

Definition nat_mod (a b : nat) :nat :=
  match b with
  | O => b
  | S b' => b' - snd (nat_divmod a b' 0 b')
  end.

Lemma identity_fn_applied_twice :
  forall (f : bool -> bool) ,
  (forall x :bool, f x = x) -> 
  forall (b :bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite <- H.
  reflexivity.
Qed.

Lemma negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall x :bool, f x = negb x) ->
  forall (b :bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  destruct b.
  - rewrite -> H. rewrite -> H. reflexivity.
  - rewrite -> H. rewrite -> H. reflexivity.
Qed.

Lemma andb_eq_orb : 
  forall n m :bool,
  (andb n m = orb n m) -> n = m.
Proof.
  intros [] [].
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
  - reflexivity.
Qed.

Inductive bin : Type :=
  | Z : bin
  | Twice : bin -> bin
  | Twice_and1: bin -> bin.

Fixpoint incr(n : bin) : bin :=
  match n with
  | Z => Twice_and1 Z
  | Twice n' => Twice_and1 n'
  | Twice_and1 n' => Twice (incr n')
  end.

Fixpoint bin_to_nat (n : bin) :nat :=
  match n with
  | Z => O
  | Twice n' => 2 * (bin_to_nat n')
  | Twice_and1 n' => 1 + 2 * (bin_to_nat n')
  end.

Example test_bin_incr1 : bin_to_nat (incr (Twice_and1 (Twice (Twice_and1 Z)))) = 
  S (bin_to_nat (Twice_and1 (Twice (Twice_and1 Z)))).
Proof.
  simpl.
  reflexivity.
Qed.