{-# OPTIONS --copattern --safe --no-sized-types --guardedness #-}
module Copattern where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream public

-- | Bisimulation as equality
record _==_ {A : Set} (x : Stream A) (y : Stream A) : Set where
  coinductive
  field
    refl-head : head x ≡ head y
    refl-tail : tail x == tail y
open _==_ public

module Introduction where

  ones : Stream ℕ
  head ones = suc zero
  tail ones = ones
  
  repeat : {A : Set} -> A -> Stream A
  repeat {A} a = P
    where
    P : Stream A
    head P = a
    tail P = repeat a
 
  even : ∀ {A} -> Stream A -> Stream A
  even {A} a = P
    where
    P : Stream A
    head P = head a
    tail P = even (tail (tail a))

  odd : ∀ {A} -> Stream A -> Stream A
  odd {A} a = P
    where
    P : Stream A
    head P = head (tail a)
    tail P = odd (tail (tail a))

module Bisimulation where
  open Introduction

  refl′ : ∀ {A} -> (a : Stream A) -> a == a
  refl′ a = f
    where
    f : a == a
    refl-head f = refl
    refl-tail f = refl′ (tail a)

  oddEven : ∀ {A} -> (a : Stream A) -> odd a == even (tail a)
  oddEven a = f
    where
    f : odd a == even (tail a)
    refl-head f = refl
    refl-tail f = oddEven ((tail (tail a)))

module Merge where
  open Bisimulation
  open Introduction

  merge : ∀ {A} -> Stream A -> Stream A -> Stream A
  merge {A} a b = ma
    where
    ma : Stream A
    head ma = head a
    tail ma = merge b (tail a)

  -- Merge! Even! Odd!
  moe : ∀ {A} -> (a : Stream A) -> (merge (even a) (odd a) == a)
  moe a = f
    where
    f : merge (even a) (odd a) == a
    refl-head f = refl
    refl-head (refl-tail f) = refl
    refl-tail (refl-tail f) = moe (tail (tail a))
