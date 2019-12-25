From Coq Require Import Arith Div2 Omega Lia Nat.

Fixpoint div_mod2 (n : nat) : (nat * bool) :=
  match n with
  | 0 => (0, false)
  | 1 => (0, true)
  | S (S n) => let (a, b) := div_mod2 n in (S a, b)
  end.

Fixpoint pow_sqr_aux (k b e : nat) : nat :=
  match k, e with
  | 0, _ => 1
  | _, 0 => 1
  | S k, _ => match div_mod2 e with
              | (e', false) => pow_sqr_aux k (b * b) e'
              | (e', true) => b * pow_sqr_aux k (b * b) e'
              end
  end.
  
Definition pow_sqr (b e : nat) : nat := pow_sqr_aux e b e.

Lemma silly:
  forall n, div_mod2 n = (div2 n, odd n).
Proof.
  induction n using (well_founded_induction lt_wf).
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  rewrite H; auto.
Qed.

Lemma pow_eq_extended:
  forall k b e,
    (k >= e) ->
    pow_sqr_aux k b e = b ^ e.
Proof.
  induction k;intros;simpl. inversion H;subst. auto.
  rewrite silly. destruct e; auto.
  generalize (lt_div2 (S e) ltac:(lia)). intros.
  assert (div2 (S e) <= k). omega. rewrite IHk.
  destruct (odd (S e)) eqn:He;
 try (rewrite (Nat.div2_odd (S e)) at 2; rewrite He;
    rewrite Nat.pow_add_r; rewrite Nat.pow_mul_r; rewrite Nat.pow_2_r;
    simpl;lia). auto. 
Qed.

Theorem pow_eq (b e : nat) : pow_sqr b e = b ^ e.
Proof. apply pow_eq_extended. auto. Qed.