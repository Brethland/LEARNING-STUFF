(* 
  This is exercises for <Software Foundations> CH14.
  Author : Brethland, Late 2019.
*)

From Coq Require Import omega.Omega.
From Coq Require Import Arith.Arith.
Add LoadPath "C:\Users\ycy12\Documents\Workspace\LEARNING-STUFF\Coq".
Load Coq19.

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).
Open Scope imp_scope.
Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (l !-> aeval st a1 ; st)
      | c1 ;; c2 =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.
Close Scope imp_scope.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.

Compute
     (test_ceval empty_st
         (X ::= 2 ;;
          IFB X ≤ 1
            THEN Y ::= 3
            ELSE Z ::= 4
          FI)).

Definition pup_to_n' : com :=
  (Y ::= 0;;
    WHILE ~(X = 0) DO
      Y ::= Y + X;;
      X ::= X - 1
    END).

Example pup_to_n_1 :
  test_ceval (X !-> 5) pup_to_n'
  = Some (0, 15, 0).
Proof. auto. Qed.

Definition peven : com :=
  (Z ::= 0 ;;
    WHILE ~(X = 0) DO
      IFB Z = 0 THEN
        Z ::= 1
      ELSE Z ::= 0 FI ;;
      X ::= X - 1
    END).

Theorem ceval_step__ceval: ∀c st st',
      (∃i, ceval_step st c i = Some st') →
      st =[ c ]⇒ st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i;intros.
  - inversion E.
  - destruct c;inversion E;subst.
    + constructor.
    + constructor. auto.
    + destruct (ceval_step st c1 i) eqn:Hei.
      ++ apply E_Seq with s. apply IHi. auto. apply IHi. auto.
      ++ inversion H0.
    + destruct (beval st b) eqn:Heb.
      ++ constructor. auto. apply IHi. auto.
      ++ apply E_IfFalse. auto. apply IHi. auto.
    + destruct (beval st b) eqn:Heb.
      ++ destruct (ceval_step st c i) eqn : Hei.
          apply E_WhileTrue with s. auto. apply IHi.
          auto. apply IHi. auto. inversion H0.
      ++ inversion H0. apply E_WhileFalse. subst. auto.
Qed.

Theorem ceval_step_more: ∀i1 i2 st st' c,
  i1 ≤ i2 →
  ceval_step st c i1 = Some st' →
  ceval_step st c i2 = Some st'.
Proof.
  induction i1; intros.
  - inversion H0.
  - destruct i2 as [|i2']. inversion H.
    assert (Hle': i1 ≤ i2') by omega.
    destruct c.
    + auto.
    + inversion H0. auto.
    + simpl in *. destruct (ceval_step st c1 i1) eqn:Hei.
      ++ apply (IHi1 i2') in Hei. rewrite Hei. auto. auto.
      ++ inversion H0.
    + simpl in *. destruct (beval st b). auto. auto.
    + simpl in *. destruct (beval st b); try auto.
      destruct (ceval_step st c i1) eqn:Hei.
      ++ apply (IHi1 i2') in Hei. rewrite Hei. auto. auto.
      ++ inversion H0.
Qed.

Theorem ceval__ceval_step: ∀c st st',
      st =[ c ]⇒ st' →
      ∃i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce.
  - exists 10. auto.
  - exists 10. simpl. rewrite H. auto.
  - destruct IHHce1. destruct IHHce2.
    destruct x. inversion H.
    exists (S x + x0). simpl. destruct x0. inversion H0.
    assert ( H' : S x <= x + S x0) by omega.
    remember (ceval_step_more _ _ _ _ _ H' H) as H1.
    rewrite H1. clear HeqH1. clear H'. clear H1.
    assert (H' : S x0 <= x + S x0) by omega.
    apply (ceval_step_more _ _ _ _ _ H' H0).
  - destruct IHHce. destruct x. inversion H0.
    exists (1 + x + 1). simpl. rewrite H.
    assert (H' : S x <= x + 1) by omega.
    apply (ceval_step_more _ _ _ _ _ H' H0).
  - destruct IHHce. destruct x. inversion H0.
    exists (1 + x + 1). simpl. rewrite H.
    assert (H' : S x <= x + 1) by omega.
    apply (ceval_step_more _ _ _ _ _ H' H0).
  - exists 1. simpl. rewrite H. auto.
  - destruct IHHce1. destruct IHHce2. destruct x. inversion H0.
    exists (S x + x0). simpl. destruct x0. inversion H1.
    rewrite H. assert ( H' : S x <= x + S x0) by omega.
    remember (ceval_step_more _ _ _ _ _ H' H0) as H2.
    rewrite H2. clear HeqH2. clear H'. clear H2.
    assert (H' : S x0 <= x + S x0) by omega.
    apply (ceval_step_more _ _ _ _ _ H' H1).
Qed.

Theorem ceval_deterministic' : ∀c st st1 st2,
     st =[ c ]⇒ st1 →
     st =[ c ]⇒ st2 →
     st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  omega. omega. Qed.
