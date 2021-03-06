(*
  Exercise for <Software Foundations> CH4.
  Author : Brethland.
*)

From Coq Require Import Arith.
From Coq Require Import Bool.

Inductive list ( X : Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check (cons nat 3 (nil nat)).

Fixpoint repeat (X : Type) (x : X) (m : nat) :=
  match m with
  | O => nil X
  | S m' => cons X x (repeat X x m')
  end.

Module Mumble.

Inductive mumble : Type :=   
  | a : mumble   
  | b : mumble -> nat -> mumble   
  | c : mumble.
 
Inductive grumble (X:Type) : Type :=   
  | d : mumble -> grumble X   
  | e : X -> grumble X.

Check c.

End Mumble.

Arguments nil {X}.
Arguments cons {X} _ _ .
Arguments repeat {X} x m.

Fixpoint app {X : Type} (l1 l2 : list X)
              : (list X) :=   
  match l1 with   
  | nil => l2   
  | cons h t => cons h (app t l2)   
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=   
  match l with   
  | nil => nil   
  | cons h t => app (rev t) (cons h nil)   
  end.

Fixpoint length {X : Type} (l : list X) : nat :=   
  match l with   
  | nil => 0   
  | cons _ l' => S (length l')   
  end.

Notation "x :: y" := (cons x y)                      
                    (at level 60, right associativity).
Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..). 
Notation "x ++ y" := (app x y)                      
                    (at level 60, right associativity).

Lemma app_nil_r : forall (X : Type) (l : list X),
  l ++ [] = l.
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    rewrite -> IHl.
    auto.
Qed.

Lemma app_assoc : forall (X : Type) (l1 l2 l3 : list X),
  l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
Proof.
  intros.
  induction l1.
  - auto.
  - simpl.
    rewrite -> IHl1.
    auto.
Qed.

Lemma app_length : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1.
  - auto.
  - simpl.
    rewrite -> IHl1.
    auto.
Qed.

Inductive prod (X Y : Type) : Type := 
  | pair : X -> Y -> prod X Y.
 
Arguments pair {X} {Y} _ _.  
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=   
  match p with   
  | (x , y) => x   
  end. 

Definition snd {X Y : Type} (p : X * Y) : Y :=   
  match p with   
  | (x , y) => y   
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
              : list (X*Y) :=   
  match lx, ly with   
  | [], _ => []   
  | _, [] => []   
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)   
  end.

Definition pair_app {X Y : Type} (l1 l2 : (list X) * (list Y)) :=
  ((fst l1) ++ (fst l2) , (snd l1) ++ (snd l2)).

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | nil => ([],[])
  | x :: t => pair_app ([fst x] , [snd x]) (split t)
  end.

Definition hd_error {X: Type} (l : list X) :=
  match l with
  | nil => None
  | x :: s => Some x
  end.


Fixpoint filter {X : Type} (f : X -> bool) (l : list X) :=
  match l with
  | [] => []
  | x :: s => if f x then x :: filter f s
                    else filter f s
  end.

Fixpoint evenb (n : nat) :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end. 

Fixpoint gtn (n m : nat) :=
  match n , m with
  | O , _ => false
  | S n' , O => true
  | S n' , S m' => gtn n' m'
  end.

Definition filter_even_gt7 (l : list nat) :=
  filter (fun s => (andb (evenb s) (gtn s 7))) l.

(* Definition regf {X : Type} (f : X -> bool) : X -> bool :=
  if f _ the*)

Definition not_b (b : bool) :=
  match b with
  | true => false
  | _    => true
  end.

Definition compose {A B C : Type} (f : B -> C) (g : A -> B) :=
  fun x => f (g x).

Check compose not_b.

Definition partition {X : Type} (f : X -> bool) (l : list X) :=
  ((filter f l) , (filter (compose not_b f) l)).

Compute (partition evenb [1;1;4;5;1;4]).

Fixpoint partition2 {X : Type} (f : X -> bool) (l : list X) :=
  match l with
  | nil      => ([], [])
  | cons x s => match f x with
                | true  => pair_app ([x] , [ ]) (partition2 f s)
                | false => pair_app ([ ] , [x]) (partition2 f s)
                end
  end.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) :=
  match l with
  | [] => []
  | x :: s => (f x) :: map f s
  end.

Lemma map_app : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros.
  induction l1.
  - auto.
  - simpl.
    rewrite <- IHl1.
    auto.
Qed.

Lemma map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    rewrite -> map_app.
    simpl.
    rewrite <- IHl.
    auto.
Qed.

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) :=
  match l with
  | [] => []
  | x :: s => f x ++ flat_map f s
  end.

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) :=
  match l with
  | [] => b
  | x :: s => f x (fold f s b)
  end.

Fixpoint beq_n (x y : nat) :=
  match x,y with
  | O, O => true
  | S x' , O => false
  | O , S y' => false
  | S x' , S y' => beq_n x' y'
  end.
Compute (fold (fun x y => andb (beq_n x 0) y) [0;1;0] true).

Definition fold_length {X : Type} (l : list X) : nat :=   
  fold (fun _ n => S n) l 0. 

Lemma fold_length_correct : forall (X : Type) (l : list X),
  fold_length l = length l.
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    rewrite <- IHl.
    unfold fold_length.
    auto.
Qed.

Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) :=
  fold (fun x n => (f x) :: n) l [].

Lemma fold_map_correct : forall (X Y : Type) (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    rewrite <- IHl.
    unfold fold_map.
    simpl.
    auto.
Qed.

Definition prod_curry {X Y Z : Type}   (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).
Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X * Y) :=
  f (fst p) (snd p).

Lemma curry_involutive : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros.
  unfold prod_curry.
  unfold prod_uncurry.
  auto.
Qed.