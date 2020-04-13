(*
  This is the exercise for <Software Foundations> V2 CH10.
  Author: Brethland, Early 2020.
*)

Require Import Strings.String.
Add LoadPath "C:\Users\ycy12\Documents\Workspace\LEARNING-STUFF\Coq".
Load Coq30.

Inductive tys : Type :=
  | Top : tys
  | Bool' : tys
  | Base : string → tys
  | Arrow' : tys → tys → tys
  | Unit : tys
.
Inductive tms : Type :=
  | var' : string → tms
  | app' : tms → tms → tms
  | abs' : string → tys → tms → tms
  | tru' : tms
  | fls' : tms
  | test' : tms → tms → tms → tms
  | unit : tms
.

Fixpoint subst (x:string) (s:tms) (t:tms) : tms :=
  match t with
  | var' y =>
      if eqb x y then s else t
  | abs' y T t1 =>
      abs' y T (if eqb x y then t1 else (subst x s t1))
  | app' t1 t2 =>
      app' (subst x s t1) (subst x s t2)
  | tru' =>
      tru'
  | fls' =>
      fls'
  | test' t1 t2 t3 =>
      test' (subst x s t1) (subst x s t2) (subst x s t3)
  | unit =>
      unit
  end.
Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Inductive value' : tms → Prop :=
  | v_abs : ∀x T t,
      value' (abs' x T t)
  | v_true :
      value' tru'
  | v_false :
      value' fls'
  | v_unit :
      value' unit
.
Hint Constructors value'.
Reserved Notation "t1 '--->' t2" (at level 40).
Inductive step' : tms → tms → Prop :=
  | ST_AppAbs : ∀x T t12 v2,
         value' v2 →
         (app' (abs' x T t12) v2) ---> [x:=v2]t12
  | ST_App1 : ∀t1 t1' t2,
         t1 ---> t1' →
         (app' t1 t2) ---> (app' t1' t2)
  | ST_App2 : ∀v1 t2 t2',
         value' v1 →
         t2 ---> t2' →
         (app' v1 t2) ---> (app' v1 t2')
  | ST_TestTrue : ∀t1 t2,
      (test' tru' t1 t2) ---> t1
  | ST_TestFalse : ∀t1 t2,
      (test' fls' t1 t2) ---> t2
  | ST_Test' : ∀t1 t1' t2 t3,
      t1 ---> t1' →
      (test' t1 t2 t3) ---> (test' t1' t2 t3)
where "t1 '--->' t2" := (step' t1 t2).
Hint Constructors step'.

Reserved Notation "T '<:' U" (at level 40).
Inductive subtype : tys → tys → Prop :=
  | S_Refl : ∀T,
      T <: T
  | S_Trans : ∀S U T,
      S <: U →
      U <: T →
      S <: T
  | S_Top : ∀S,
      S <: Top
  | S_Arrow : ∀S1 S2 T1 T2,
      T1 <: S1 →
      S2 <: T2 →
      (Arrow' S1 S2) <: (Arrow' T1 T2)
where "T '<:' U" := (subtype T U).

Hint Constructors subtype.
Module Examples.
Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation z := "z".
Notation A := (Base "A").
Notation B := (Base "B").
Notation C := (Base "C").
Notation String := (Base "String").
Notation Float := (Base "Float").
Notation Integer := (Base "Integer").
Example subtyping_example_0 :
  (Arrow' C Bool') <: (Arrow' C Top).
  (* C->Bool <: C->Top *)
Proof. auto. Qed.

End Examples.

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

Definition context := partial_map tys.
Reserved Notation "Gamma '⊢' t '∈' T" (at level 40).
Inductive has_type' : context → tms → tys → Prop :=
  (* Same as before *)
  | T_Var : ∀Gamma x T,
      Gamma x = Some T →
      Gamma ⊢ var' x ∈ T
  | T_Abs : ∀Gamma x T11 T12 t12,
      (x ⊢> T11 ; Gamma) ⊢ t12 ∈ T12 →
      Gamma ⊢ abs' x T11 t12 ∈ Arrow' T11 T12
  | T_App : ∀T1 T2 Gamma t1 t2,
      Gamma ⊢ t1 ∈ Arrow' T1 T2 →
      Gamma ⊢ t2 ∈ T1 →
      Gamma ⊢ app' t1 t2 ∈ T2
  | T_True : ∀Gamma,
       Gamma ⊢ tru' ∈ Bool'
  | T_False : ∀Gamma,
       Gamma ⊢ fls' ∈ Bool'
  | T_Test' : ∀t1 t2 t3 T Gamma,
       Gamma ⊢ t1 ∈ Bool' →
       Gamma ⊢ t2 ∈ T →
       Gamma ⊢ t3 ∈ T →
       Gamma ⊢ test' t1 t2 t3 ∈ T
  | T_Unit : ∀Gamma,
      Gamma ⊢ unit ∈ Unit
  | T_Sub : ∀Gamma t S T,
      Gamma ⊢ t ∈ S →
      S <: T →
      Gamma ⊢ t ∈ T

where "Gamma '⊢' t '∈' T" := (has_type' Gamma t T).
Hint Constructors has_type'.

Hint Extern 2 (has_type' _ (app' _ _) _) =>
  eapply T_App; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.
Module Examples2.
  Import Examples.

End Examples2.

