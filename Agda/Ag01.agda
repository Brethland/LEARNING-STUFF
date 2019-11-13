module Ag01 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero *  n = zero
suc m * n = n + (m * n)

_ : 3 * 4 ≡ 12
_ = refl

_^_ : ℕ → ℕ → ℕ
m ^ 0       = 1
m ^ (suc n) = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ = refl

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

infixl 6 _+_ _∸_
infixl 7 _*_

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil    = nil
inc (x1 b) = x0 (inc b)
inc (x0 b) = x1 b

_ : inc (x0 nil) ≡ (x1 nil)
_ = refl

_ : inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil
_ = refl

to : ℕ → Bin
to zero = x0 nil
to (suc m) = inc (to m)

from : Bin → ℕ
from nil      = zero
from (x1 b)   = suc (2 * (from b))
from (x0 b)   = 2 * (from b)

