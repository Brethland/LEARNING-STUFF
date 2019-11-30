module Ag07 where

open import IO

data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) → (b : B a → W A B) → W A B

module WBinTree where
  data Tree : Set where
    Leaf : Tree
    Node : Tree
  
  data Direction : Set where
    Left  : Direction
    Right : Direction

  data Bottom : Set where

  void : ∀ {A : Set} → Bottom → A
  void ()

  binTree : Tree → Set
  binTree Leaf = Bottom
  binTree Node = Direction

  BinTree : Set
  BinTree = W Tree binTree

  leaf : BinTree
  leaf = sup Leaf void

  node : BinTree → BinTree → BinTree
  node x y = sup Node λ {
    Left  → x ;
    Right → y }
