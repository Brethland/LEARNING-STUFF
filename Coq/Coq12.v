(*
  This is exercises from <Software Foundations> CH7.
  Author : Brethland, Late 2019.
*)

From Coq Require Import Nat.
From Coq Require Import Unicode.Utf8.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_ss : forall n : nat, ev n -> ev (S (S n)).

Fixpoint double (n : nat) :=
  match n with
  | 0 => 0
  | S n' => S (S (double n'))
  end.

Lemma ev_double : forall n : nat, ev (double n).
Proof.
  intros.
  induction n.
  - simpl. apply ev_0.
  - simpl.
    apply ev_ss.
    auto.
Qed.

Lemma ev_minus2 : forall n, ev n -> ev (pred (pred n)).
Proof.
  intros.
  inversion H.
  - simpl. apply ev_0.
  - simpl. apply H0.
Qed.

Lemma evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros.
  inversion H.
  apply H1.
Qed.

Lemma evSSSS_ev : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Lemma even5_nonsense : ev 5 -> 2 + 2 = 9.
Proof.
  intros.
  inversion H.
  inversion H1. inversion H3.
Qed.

Lemma ev_even' : forall n, ev n -> exists k, n = double k.
Proof.
  intros.
  inversion H.
  - exists 0. auto.
  - simpl.
    assert (I : (∃ k', n0 = double k') →
            (∃ k, S (S n0) = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k').
      auto. }
    apply I. Abort.

Lemma ev_even : ∀ n, ev n → ∃ k, n = double k. 
Proof.
  intros.
  induction H.
  - exists 0. auto.
  - destruct IHev.
    rewrite H0.
    exists (S x).
    auto.
Qed.

Theorem ev_even_iff : ∀ n,   
  ev n ↔ ∃ k, n = double k. 
Proof.   intros n. split.   
  - (* -> *) apply ev_even.   
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double. 
Qed.

Lemma ev_sum : forall n m , ev n -> ev m -> ev (n + m).
Proof.
  intros.
  generalize dependent m.
  induction H.
  - intros. simpl. apply H0.
  - intros. apply IHev in H0.
    simpl. apply ev_ss. auto.
Qed.

Inductive ev' : nat → Prop := 
  | ev'_0 : ev' 0 
  | ev'_2 : ev' 2 
  | ev'_sum : ∀ n m, ev' n → ev' m → ev' (n + m).


Lemma S_injective : forall n m, n = m -> S n = S m.
Proof.
  intros.
  rewrite H. auto.
Qed.

Lemma silly : forall n, S (S n) = n + 2.
Proof.
  intros.
  induction n.
  - auto.
  - simpl. apply S_injective. auto.
Qed.
 
Lemma ev_ev' : forall n, ev n <-> ev' n.
Proof.
  split.
  - intros.
    induction H. 
    + apply ev'_0.
    + rewrite silly. apply ev'_sum.
      auto. apply ev'_2.
  - intros.
    induction H.
    + apply ev_0.
    + apply ev_ss. apply ev_0.
    + apply ev_sum. auto. auto.
Qed.

Lemma ev_ev__ev : forall n m, ev (n + m) -> ev n -> ev m.
Proof.
  intros.
  generalize dependent m.
  induction H0.
  - intros. simpl in H. auto.
  - intros. simpl in H. inversion H.
    apply IHev. auto.
Qed.

Require Import Coq.Setoids.Setoid.
Require Import PeanoNat.
Require Import Arith.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros. induction n.
  - auto.
  - simpl. rewrite <- plus_n_Sm.
    apply S_injective. apply S_injective. auto.
Qed.

Lemma silly_another : forall n m p, n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite plus_assoc. rewrite plus_assoc.
  rewrite (@plus_comm n m). auto.
Qed.

Theorem ev_plus_plus : forall n m p, ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p H.
  apply ev_ev__ev.
  rewrite plus_comm.
  rewrite silly_another.
  rewrite <- plus_assoc.
  rewrite plus_assoc.
  apply ev_sum.
  apply H.
  rewrite <- double_plus.
  apply ev_double.
Qed.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, le n m -> le n (S m).

Notation "m ≤ n" := (le m n).
Notation "m <= n" := (le m n).

Definition lt (n m:nat) := le (S n) m. 
Notation "m < n" := (lt m n).

Inductive square_of : nat → nat → Prop :=   
  | sq : ∀ n:nat, square_of n (n * n). 
Inductive next_nat : nat → nat → Prop :=   
  | nn : ∀ n:nat, next_nat n (S n). 
Inductive next_even : nat → nat → Prop :=   
  | ne_1 : ∀ n, ev (S n) → next_even n (S n)   
  | ne_2 : ∀ n, ev (S (S n)) → next_even n (S (S n)).

Inductive total_relation : nat -> nat -> Prop :=
  | tl : forall n m, (le n m) \/ (le m n) -> total_relation n m.
Inductive empty_relation : nat -> nat -> Prop :=
  | el : forall n, next_nat (S n) n -> empty_relation n (S n).

Lemma le_trans : forall n m o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  induction H0.
  - auto.
  - apply le_S. apply IHle. auto.
Qed.

Lemma O_le_n : forall n, 0 <= n.
Proof.
  intros.
  induction n.
  - apply le_n.
  - apply le_S. auto.
Qed.

Lemma n_le_m__Sn_le_Sm : forall n m, n <= m -> S n <= S m.
Proof.
  intros.
  induction H.
  - apply le_n.
  - apply le_S. auto.
Qed.

Lemma Sn_le_m__n_le_m : forall n m, S n <= m -> n <= m.
Proof.
  intros.
  induction m.
  - inversion H.
  - inversion H.
    + apply le_S. apply le_n.
    + apply le_S. apply IHm. auto.
Qed.

Lemma Sn_le_Sm__n_le_m : forall n m, S n <= S m -> n <= m.
Proof.
  intros.
  inversion H.
  - apply le_n.
  - apply Sn_le_m__n_le_m in H2.
    auto.
Qed.

Lemma le_plus_l : forall a b, a <= a + b.
Proof.
  intros.
  induction b.
  - rewrite plus_comm. simpl. apply le_n.
  - rewrite <- plus_n_Sm. apply le_S. auto.
Qed.

Require Import Lia.

Lemma fuck : forall a b c, a + b <= c -> a <= c /\ b <= c.
Proof.
  induction a;intros;split;simpl in *;auto. apply O_le_n.
  destruct c. inversion H. 
  1 : apply n_le_m__Sn_le_Sm;apply Sn_le_Sm__n_le_m in H.
  2 : apply Sn_le_m__n_le_m in H.
  1 - 2 : apply IHa in H;inversion H;auto.
Qed.

Lemma silly1 : forall a b c d, a + b <= c + d -> a <= c \/ b <= d.
Proof.
  induction a;intros.
  - left. apply O_le_n.
  - destruct c;replace (0 + d) with d by auto. right. apply fuck in H;inversion H;auto.
    simpl in *. apply Sn_le_Sm__n_le_m in H. apply IHa in H. destruct H;auto.
    left. apply n_le_m__Sn_le_Sm;auto.
Qed.

Lemma plus_lt : forall n1 n2 m, n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros.
  split.
  - induction n2.
    + rewrite plus_comm in H. simpl. auto.
    + rewrite <- plus_n_Sm in H. apply Sn_le_m__n_le_m in H.
      apply IHn2 in H. auto.
  - induction n1.
    + simpl in H. auto.
    + rewrite plus_comm in H. rewrite <- plus_n_Sm in H.
      apply Sn_le_m__n_le_m in H. rewrite plus_comm in H. 
      apply IHn1 in H. auto.
Qed.

Lemma lt_S : forall n m, n < m -> n < S m.
Proof.
  unfold lt.
  intros.
  apply le_S. auto.
Qed.

Lemma leb_complete : forall n m, leb n m = true -> n <= m.
Proof.
  intros.
  generalize dependent m.
  induction n.
  - intros. apply O_le_n.
  - intros.
    destruct m.
    + inversion H.
    + apply n_le_m__Sn_le_Sm. apply IHn.
      inversion H. auto.
Qed.

Lemma leb_injective : forall n, leb n n = true.
Proof.
  intros.
  induction n.
  - auto.
  - simpl. auto.
Qed. 

Lemma leb_correct : forall n m, n <= m -> leb n m = true.
Proof.
  intros.
  generalize dependent n.
  induction m.
  - intros. inversion H. auto.
  - intros. inversion H.
    + simpl. apply leb_injective.
    + apply IHm in H2.
      destruct n.
      ++ auto.
      ++ simpl.
         apply IHm.
         apply Sn_le_Sm__n_le_m in H. auto.
Qed.

Lemma leb_true_trans : forall n m o, leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  intros.
  apply leb_complete in H. apply leb_complete in H0.
  apply leb_correct.
  apply (@le_trans m n o). auto. auto.
Qed.

Lemma leb_iff : forall n m, leb n m = true <-> n <= m.
Proof.
  intros.
  split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Definition fR : nat -> nat -> nat :=
  (fun n m => (n + m)).

Inductive R : nat → nat → nat → Prop :=
  | c1 : R 0 0 0
  | c2 : ∀ m n o, R m n o → R (S m) n (S o)
  | c3 : ∀ m n o, R m n o → R m (S n) (S o).

(* R m (S n) (S o) = R (S m) n (S o) *)

Lemma R_O : forall n, R 0 n n.
Proof.
  intros. induction n.
  - apply c1.
  - apply c3. auto.
Qed.

Lemma R_O_r : forall n, R n 0 n.
Proof.
  induction n.
  - apply c1.
  - apply c2. auto.
Qed.

Theorem R_equiv_fR : ∀ m n o, R m n o ↔ fR m n = o. 
Proof. 
  split.
  - intros. unfold fR.
    induction H.
    + auto.
    + rewrite plus_comm. rewrite <- plus_n_Sm. rewrite <- IHR. 
      rewrite plus_comm. auto.
    + rewrite <- plus_n_Sm. rewrite IHR. auto.
  - unfold fR.
    generalize dependent n. generalize dependent o.
    induction m.
    + intros. simpl in H. rewrite H.
      apply R_O.
    + intros. generalize dependent o. induction n.
      intros.
      ++ rewrite plus_comm in H. simpl in H. rewrite H. apply R_O_r.
      ++ intros.
         simpl in H. rewrite <- plus_n_Sm in H.
         rewrite <- H. apply c3. apply IHn. auto.
Qed.

Inductive subseq : (list nat) -> (list nat) -> Prop :=
  | nil_sub : subseq nil nil
  | app1 : forall (l1 l2 : list nat) (x : nat), subseq l1 l2 -> subseq l1 (x :: l2)
  | app2 : forall (l1 l2 : list nat) (x : nat), subseq l1 l2 -> subseq (x :: l1) (x :: l2).

Require Import List.

Lemma subseq_refl : forall (l : list nat), subseq l l.
Proof.
  intros.
  induction l.
  - apply nil_sub.
  - apply app2. auto.
Qed.

Lemma subseq_nil : forall l, subseq nil l.
Proof.
  intros.
  induction l.
  - apply nil_sub.
  - apply app1.
    auto.
Qed.

Lemma cons_app : forall l1 l2 (x : nat), (x :: l1) ++ l2 = x :: (l1 ++ l2).
Proof.
  intros.
  generalize dependent l2.
  induction l1.
  - intros. simpl. auto.
  - intros. simpl. auto.
Qed.

Lemma subseq_app : forall l1 l2 l3, subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros.
  induction H.
  - simpl. apply subseq_nil.
  - rewrite cons_app. apply app1. auto.
  - rewrite cons_app. apply app2. auto.
Qed.

Lemma subseq_trans : forall l1 l2 l3, subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros.  generalize dependent H. generalize dependent l1.
  induction H0.
  - intros. inversion H. apply nil_sub.
  - intros. apply app1. apply IHsubseq. auto.
  - intros. inversion H.
    + apply app1. apply IHsubseq. auto.
    + apply app2. apply IHsubseq. auto.
Qed.  

