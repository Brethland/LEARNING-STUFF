(*
  Some exercises come from Software Foundations Book1 CH3.
  Author : Brethland.
*)

Fixpoint evenb(n : nat) :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair n m => n
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair n m => m
  end.

Notation "( x , y )" := (pair x y).

Definition swap (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Lemma snd_fst_is_swap : forall p : natprod, (snd p, fst p) = swap p.
Proof.
  intros.
  destruct p as [n m].
  simpl.
  auto.
Qed.

Lemma fst_swap_is_snd : forall p : natprod, fst (swap p) = snd p.
Proof.
  intros.
  destruct p as [n m].
  simpl.
  auto.
Qed.

Inductive natlist: Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l)
                      (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Fixpoint repeat (n count : nat) :natlist :=
  match count with
  | O => nil
  | S count' => cons n (repeat n count')
  end.

Fixpoint length (p : natlist) : nat :=
  match p with
  | nil => O
  | x :: l => S (length l)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | x :: y => x :: (app y l2)
  end.

Notation "x ++ y" := (app x y)
                      (right associativity , at level 60).

Definition hd(default : nat) (l : natlist) :=
  match l with
  | nil => default
  | x :: y => x
  end.

Definition tl(l : natlist) := 
  match l with
  | nil => nil
  | x :: y => y
  end.

Fixpoint beq_n (n m :nat) :=
  match n , m with
  | O, O => true
  | O, S m' => false
  | S n', O => false
  | S n', S m' => beq_n n' m'
  end.

Fixpoint nonzero (l : natlist) :=
  match l with
  | nil => nil
  | x :: y => if beq_n x O then nonzero y
                            else x :: nonzero y
  end.

Fixpoint oddnumbers (l : natlist) :=
  match l with 
  | nil => nil
  | x :: y => match evenb x with 
                    | true => oddnumbers y
                    | false => x :: oddnumbers y
                    end
  end.

Definition conutoddnumbers (l : natlist) :=
  length (oddnumbers l).

Inductive tree a :=
  | leaf
  | node : tree a -> a -> tree a -> tree a.

Check nat_rect.
Check nat_ind.
Check nat_rec.


Check tree_ind.

Fixpoint alternative (l1 l2 : natlist ) :natlist :=
  match l1,l2 with
  | nil,_ => l2
  | _,nil => l1
  | x :: y , z :: p => x :: z :: (alternative y p)
  end.

Definition bag := natlist.

Fixpoint count (ele: nat) (s : bag) :=
  match s with
  | nil => O
  | x :: y => match beq_n ele x with
              | true => S (count ele y)
              | false => count ele y
            end
  end.

 