Require Import List Arith Omega Lia.
Import ListNotations.

Inductive expr : Type :=
| Const : nat -> expr
| Plus : expr -> expr -> expr.

Fixpoint eval_expr (e : expr) : nat := 
  match e with
  | Const n => n
  | Plus e1 e2 => eval_expr e1 + eval_expr e2
  end.

Fixpoint eval_expr_tail' (e : expr) (acc : nat) : nat :=
  match e with
  | Const n => n + acc
  | Plus e1 e2 => eval_expr_tail' e2 (eval_expr_tail' e1 acc)
  end.

Definition eval_expr_tail e := eval_expr_tail' e 0.

Fixpoint eval_expr_cont' {A} (e : expr) (k : nat -> A) : A :=
  match e with
  | Const n => k n
  | Plus e1 e2 => eval_expr_cont' e2 (fun n2 =>
                  eval_expr_cont' e1 (fun n1 => k (n1 + n2)))
  end.

Definition eval_expr_cont (e : expr) : nat :=
  eval_expr_cont' e (fun n => n).

Lemma silly1 : forall e n, eval_expr_tail' e n = n + eval_expr_tail' e 0.
Proof.
  induction e;intros;simpl. omega.
  rewrite (IHe1 n). rewrite (IHe2 (n + eval_expr_tail' e1 0)).
  rewrite (IHe2 (eval_expr_tail' e1 0)). omega.
Qed.

Theorem eval_expr_tail_correct : forall e, eval_expr_tail e = eval_expr e.
Proof.
  induction e;unfold eval_expr_tail in *;simpl.
  omega. rewrite IHe1. rewrite silly1. auto.
Qed.

Lemma silly2 : forall {A : Type} e (k : nat -> A), eval_expr_cont' e k
                            = k (eval_expr e).
Proof.
  induction e;intros;simpl. auto.
  rewrite (IHe2 (fun n2 : nat => eval_expr_cont' e1 (fun n1 : nat => k (n1 + n2)))).
  rewrite (IHe1 (fun n1 : nat => k (n1 + eval_expr e2))). auto.
Qed.

Theorem eval_expr_cont_correct : forall e, eval_expr_cont e = eval_expr e.
Proof.
  induction e;unfold eval_expr_cont in *;simpl. auto.
  rewrite (silly2 _ (fun n2 : nat => eval_expr_cont' e1 (fun n1 : nat => n1 + n2))).
  rewrite (silly2 _ (fun n1 : nat => n1 + eval_expr e2)). auto.
Qed.

Inductive instr := Push (n : nat) | Add.

Definition prog := list instr.

Definition stack := list nat.

Fixpoint run (p : prog) (s : stack) : stack := 
  match p with
  | [] => s
  | i :: p' => let s' :=
                  match i with
                  | Push n => n :: s
                  | Add => match s with
                          | a1 :: a2 :: s' => a1 + a2 :: s'
                          | _ => s
                          end
                  end in
              run p' s'
  end.

Fixpoint compile (e : expr) : prog :=
  match e with
  | Const n => [Push n]
  | Plus e1 e2 => compile e1 ++ compile e2 ++ [Add]
  end.

Lemma silly3 : forall p1 p2 s, run (p1 ++ p2) s = run p2 (run p1 s).
Proof. induction p1;intros;simpl;auto. Qed.

Theorem compile_correct_extend : forall e s, run (compile e) s = eval_expr e :: s.
Proof.
  induction e;intros;simpl;auto.
  repeat rewrite silly3. rewrite IHe2. rewrite IHe1. simpl. rewrite plus_comm. auto.
Qed.

Theorem compile_correct : forall e, run (compile e) [] = [eval_expr e].
Proof. intros; apply (compile_correct_extend e []). Qed.