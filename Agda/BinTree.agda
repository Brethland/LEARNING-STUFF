{-# OPTIONS --sized-types #-}
module BinTree where

open import Data.Nat
open import Data.List
open import Data.List.Properties
open import Size

data Bin {T : Set} {i : Size} : Set where
  Leaf : Bin {T} {i}
  Node : T → Bin {T} {i} → Bin {T} {i} → Bin {T} {i}

data Rose {T : Set} {i : Size} : Set where
  Empty : Rose {T} {i}
  R : T → List (Rose {T} {i}) → Rose {T} {i}

BinListToBin : {T : Set} → List (Bin {T}) → Bin {T}
BinListToBin [] = Leaf
BinListToBin (Leaf ∷ bs) = BinListToBin bs
BinListToBin (Node x b b₁ ∷ bs) = Node x b (BinListToBin bs)

Seperate : {T : Set} → Bin {T} → List (Bin {T})
Seperate Leaf = []
Seperate (Node x b b₁) = Node x b Leaf ∷ Seperate b₁

RoseToBin : {i : Size} → {T : Set} → Rose {T} {∞} → Bin {T} {∞}
RoseToBin Empty = Leaf
RoseToBin (R x x₁) = Node x (BinListToBin (map RoseToBin x₁)) Leaf

BinToRose : {T : Set} → Bin {T} → Rose {T}
BinToRose Leaf = Empty
BinToRose (Node x b b₁) = R x (map BinToRose (Seperate b₁))
