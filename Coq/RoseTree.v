From Coq Require Import Arith List.

Import List Notations.

Inductive BinTree (T : Type) : Type :=
  | Leaf
  | Node (val : T) (left right : BinTree T).

Inductive RoseTree (T : Type) : Type :=
  | Empty
  | Rose (val : T) (rose : list (RoseTree T)).

Fixpoint seperateBin (T : Type) (bin : BinTree T) : list (BinTree T) :=
  match bin with
   | Node _ v l r => Node _ v (Leaf _) (Leaf _) :: seperateBin T l ++ seperateBin T r
   | _          => nil
  end.

Fixpoint binToRoseAux (T : Type) (bin : BinTree T) : list (BinTree _) :=
  match bin with
  | Node _ v l r => (Node _ v (Leaf _) (Leaf _)) :: seperateBin _ l
  | Leaf _       => nil
  end.

Fixpoint binToRose (T : Type) (binL : list (BinTree T)) : RoseTree T :=
  match binL with
  | b :: bs      => match b with
                     | Node _ v _ _ => Rose _ v (binToRose _ bs :: nil)
                     | _            => Empty _
                    end
  | nil          => Empty _
  end.

Definition sillyBin : BinTree nat := (Node _ 1 (Node _ 2 (Node _ 3 (Leaf _) (Leaf _)) (Node _ 4 (Leaf _) (Leaf _))) (Node _ 0 (Leaf _) (Leaf _))).

Compute binToRose _ (binToRoseAux _ sillyBin).
