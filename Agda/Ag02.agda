module Ag02 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎

+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + 0 ≡ m
+-identityʳ zero =
  begin
    zero + 0
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    m + (n + p) + q
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p                           = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p) | +-comm m n | +-assoc n m p = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ 0 n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | +-assoc p (m * p) (n * p) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc 0 n p = refl
*-assoc (suc m) n p rewrite  *-distrib-+ n (m * n) p | *-assoc m n p = refl

*-identityʳ : ∀ (n : ℕ) → n * 0 ≡ 0
*-identityʳ 0 = refl
*-identityʳ (suc n) rewrite *-identityʳ n = refl

*-suc : ∀ (m n : ℕ) → m * (suc n) ≡ m + m * n
*-suc 0 n = refl
*-suc (suc m) n rewrite *-suc m n | +-swap n m (m * n) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm 0 n rewrite *-identityʳ n = refl
*-comm (suc m) n rewrite *-comm m n | *-suc n m = refl

∸-n : ∀ (n : ℕ) → 0 ∸ n ≡ 0
∸-n zero = refl
∸-n (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p rewrite ∸-n n | ∸-n p | ∸-n (n + p) = refl
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

^-distrib-+ : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distrib-+ m 0 p rewrite +-identityʳ (m ^ p) = refl
^-distrib-+ m (suc n) p rewrite ^-distrib-+ m n p | *-assoc m (m ^ n) (m ^ p) = refl

^-distrib-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distrib-* m n zero = refl
^-distrib-* m n (suc p) rewrite ^-distrib-* m n p | sym (*-assoc (m * n) (m ^ p) (n ^ p))
  | *-assoc m n (m ^ p) | *-comm n (m ^ p) | *-assoc m ((m ^ p) * n) (n ^ p) | *-assoc (m ^ p) n (n ^ p)
  | *-assoc m (m ^ p) (n * (n ^ p)) = refl



^-identity : ∀ (p : ℕ) → 1 ^ p ≡ 1
^-identity zero = refl
^-identity (suc p) rewrite ^-identity p = refl

^-*-plus : ∀ (m n p : ℕ) → m ^ (n * p) ≡ (m ^ n) ^ p
^-*-plus m zero p rewrite ^-identity p = refl
^-*-plus m (suc n) p rewrite ^-distrib-+ m p (n * p) | ^-*-plus m n p | sym (^-distrib-* m (m ^ n) p) = refl

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil    = x1 nil
inc (x1 b) = x0 (inc b)
inc (x0 b) = x1 b

to : ℕ → Bin
to zero = nil
to (suc m) = inc (to m)

from : Bin → ℕ
from nil      = zero
from (x1 b)   = suc (2 * (from b))
from (x0 b)   = 2 * (from b)

inc-suc : ∀ (x : Bin) → from (inc x) ≡ suc (from x)
inc-suc nil = refl
inc-suc (x0 x) = refl
inc-suc (x1 x) rewrite inc-suc x | +-suc (from x) (from x + 0) = refl
