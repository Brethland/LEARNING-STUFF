(*
  Exercises for <Software Foundations> V2 CH7.
  Author : Brethand, Early 2020.
*)

Set Warnings "-notation-overridden,-parsing".
Require Import Strings.String.
Add LoadPath "C:\Users\ycy12\Documents\Workspace\LEARNING-STUFF\Coq".
Load Coq29.

Module STLC.

Inductive ty : Type :=
  | Bool : ty
  | Arrow : ty → ty → ty.

Inductive tm : Type :=
  | var : string → tm
  | app : tm → tm → tm
  | abs : string → ty → tm → tm
  | tru : tm
  | fls : tm
  | test : tm → tm → tm → tm.

Open Scope string_scope.
Definition x := "x".
Definition y := "y".
Definition z := "z".
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

Notation idB :=
  (abs x Bool (var x)).

Notation idBB :=
  (abs x (Arrow Bool Bool) (var x)).

Notation k := (abs x Bool (abs y Bool (var x))).

Notation notB := (abs x Bool (test (var x) fls tru)).

Inductive value : tm → Prop :=
  | v_abs : ∀x T t,
      value (abs x T t)
  | v_tru :
      value tru
  | v_fls :
      value fls.
Hint Constructors value.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var x' =>
      if eqb x x' then s else t
  | abs x' T t1 =>
      abs x' T (if eqb x x' then t1 else ([x:=s] t1))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  | tru =>
      tru
  | fls =>
      fls
  | test t1 t2 t3 =>
      test ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Inductive substi (s : tm) (x : string) : tm → tm → Prop :=
  | s_tru : substi s x tru tru
  | s_fls : substi s x fls fls
  | s_var1 :
      substi s x (var x) s
  | s_var2 : forall y, eqb x y = false -> substi s x (var y) (var y)
  | s_abs1 :
      forall y T t1 t2, eqb x y = false ->
                  substi s x t1 t2 -> substi s x (abs y T t1) (abs y T t2)
  | s_abs2 : forall y T t1, eqb x y = true ->
                  substi s x (abs y T t1) (abs y T t1)
  | s_app : forall t1 t2 t1' t2', substi s x t1 t1' -> substi s x t2 t2' ->
                                substi s x (app t1 t2) (app t1' t2')
  | s_test : forall t1 t2 t3 t1' t2' t3', substi s x t1 t1' -> substi s x t2 t2' ->
                               substi s x t3 t3' -> substi s x (test t1 t2 t3) (test t1' t2' t3').

Hint Constructors substi.
Theorem substi_correct : ∀s x t t',
  [x:=s]t = t' ↔ substi s x t t'.
Proof with auto.
  split.
  - intros. generalize dependent t'. induction t;intros;simpl in *.
    destruct (x0 =? s0) eqn:Heq;subst. destruct (eqb_spec x0 s0) in Heq;subst. constructor.
    inversion Heq. constructor...
    rewrite <- H. constructor. eapply IHt1... eapply IHt2...
    destruct (x0 =? s0) eqn:Heq;subst. apply s_abs2... constructor. auto. eapply IHt...
    1 - 3 : rewrite <- H;constructor. 
    eapply IHt1;auto. eapply IHt2;auto. eapply IHt3;auto.
  - intros. induction H;subst;simpl;auto.
    assert (x0 =? x0 = true). assert(x0 = x0) by auto. destruct (eqb_spec x0 x0) in H;subst.
    auto. exfalso. apply n... 1 - 2 : rewrite H...
    1 - 2 : rewrite H...
Qed.

Reserved Notation "t1 '-->>' t2" (at level 40).
Inductive step : tm → tm → Prop :=
  | ST_AppAbs : ∀x T t12 v2,
         value v2 →
         (app (abs x T t12) v2) -->> [x:=v2]t12
  | ST_App1 : ∀t1 t1' t2,
         t1 -->> t1' →
         app t1 t2 -->> app t1' t2
  | ST_App2 : ∀v1 t2 t2',
         value v1 →
         t2 -->> t2' →
         app v1 t2 -->> app v1 t2'
  | ST_TestTru : ∀t1 t2,
      (test tru t1 t2) -->> t1
  | ST_TestFls : ∀t1 t2,
      (test fls t1 t2) -->> t2
  | ST_Test : ∀t1 t1' t2 t3,
      t1 -->> t1' →
      (test t1 t2 t3) -->> (test t1' t2 t3)

where "t1 '-->>' t2" := (step t1 t2).
Hint Constructors step.
Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Definition partial_map (A : Type) := total_map (option A).
Definition empty {A : Type} : partial_map A :=
  t_empty None.
Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '⊢>' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).
Notation "x '⊢>' v" := (update empty x v)
  (at level 100).

Definition context := partial_map ty.

Reserved Notation "Gamma '⊢' t '∈' T" (at level 40).
Inductive has_type : context → tm → ty → Prop :=
  | T_Var : ∀Gamma x T,
      Gamma x = Some T →
      Gamma ⊢ var x ∈ T
  | T_Abs : ∀Gamma x T11 T12 t12,
      (x ⊢> T11 ; Gamma) ⊢ t12 ∈ T12 →
      Gamma ⊢ abs x T11 t12 ∈ Arrow T11 T12
  | T_App : ∀T11 T12 Gamma t1 t2,
      Gamma ⊢ t1 ∈ Arrow T11 T12 →
      Gamma ⊢ t2 ∈ T11 →
      Gamma ⊢ app t1 t2 ∈ T12
  | T_Tru : ∀Gamma,
       Gamma ⊢ tru ∈ Bool
  | T_Fls : ∀Gamma,
       Gamma ⊢ fls ∈ Bool
  | T_Test : ∀t1 t2 t3 T Gamma,
       Gamma ⊢ t1 ∈ Bool →
       Gamma ⊢ t2 ∈ T →
       Gamma ⊢ t3 ∈ T →
       Gamma ⊢ test t1 t2 t3 ∈ T

where "Gamma '⊢' t '∈' T" := (has_type Gamma t T).
Hint Constructors has_type.

Theorem t_update_neq : ∀(A : Type) (m : total_map A) x1 x2 v,
    x1 ≠ x2 →
    (x1 !-> v ; m) x2 = m x2.
Proof.
  intros.
  unfold t_update. apply beq_string_false_iff in H.
  rewrite H. auto.
Qed.

Example typing_example_3 :
  exists T,
    empty ⊢
      (abs x (Arrow Bool Bool)
         (abs y (Arrow Bool Bool)
            (abs z Bool
               (app (var y) (app (var x) (var z)))))) ∈
      T.
Proof with auto.
  exists (Arrow (Arrow Bool Bool) (Arrow (Arrow Bool Bool) (Arrow Bool Bool))).
  do 3 apply T_Abs. apply T_App with Bool. apply T_Var. unfold update. apply t_update_neq.
  assert(z =? y = false) by auto. destruct (eqb_spec z y) in H. inversion H. auto.
  apply T_App with Bool. apply T_Var. unfold update. apply t_update_neq.
  assert(z =? x = false) by auto. destruct (eqb_spec z x) in H. inversion H. auto.
  apply T_Var. unfold update. apply t_update_eq.
Qed.

Example typing_nonexample_1 :
  ¬∃T,
      empty ⊢
        (abs x Bool
            (abs y Bool
               (app (var x) (var y)))) ∈
        T.
Proof.
  intros Hc. inversion Hc.
  (* The clear tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
  inversion H. subst. clear H.
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  inversion H5. subst. clear H5.
  inversion H1. Qed.

Example typing_nonexample_3 :
  ¬(∃S T,
        empty ⊢
          (abs x S
             (app (var x) (var x))) ∈
          T).
Proof.
  intros Hc. inversion Hc. inversion H. clear Hc. clear H.
  inversion H0;subst;clear H0.
  inversion H5;subst;clear H5.
  inversion H4;subst;clear H4.
  inversion H1;subst. inversion H2;subst.
  inversion H3. clear H1. clear H2. clear H3.
  induction T11. inversion H0. inversion H0;subst. apply IHT11_1. auto.
Qed.

End STLC.