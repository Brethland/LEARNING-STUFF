Inductive list ( X : Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check (cons nat 3 (nil nat)).

Fixpoint repeat (X : Type) (x : X) (m : nat) :=
  match m with
  | O => nil X
  | S m' => cons X x (repeat X x m')
  end.

Inductive mumble : Type :=   
  | a : mumble   
  | b : mumble -> nat -> mumble   
  | c : mumble.
 
Inductive grumble (X:Type) : Type :=   
  | d : mumble -> grumble X   
  | e : X -> grumble X.

Check c.

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

