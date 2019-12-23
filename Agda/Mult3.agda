{-# OPTIONS --without-K --safe #-}
module Mult3 where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

data Mult3 : ℕ → Set where
  0-mult : Mult3 0
  SSS-mult : ∀ n → Mult3 n → Mult3 (suc (suc (suc n)))

data Mult3' : ℕ → Set where
  30-mult : Mult3' 30
  21-mult : Mult3' 21
  sum-mult : ∀ n m → Mult3' n → Mult3' m → Mult3' (n + m)
  diff-mult : ∀ l n m → Mult3' n → Mult3' m → l + n ≡ m → Mult3' l

silly3 : Mult3' 3
silly3 = diff-mult 3 9 12 (diff-mult 9 21 30 21-mult 30-mult refl) (diff-mult 12 9 21 (diff-mult 9 21 30 21-mult 30-mult refl) 21-mult refl) refl

lemma-plus : ∀ {n m : ℕ} → Mult3 n → Mult3 m → Mult3 (n + m)
lemma-plus 0-mult m = m
lemma-plus {m = m₁} (SSS-mult n n₁) m = SSS-mult (n + m₁) (lemma-plus n₁ m)

lemma-minus : ∀ {l n : ℕ} → Mult3 n → Mult3 (n + l) → Mult3 l
lemma-minus {l} {.0} 0-mult m₁ = m₁
lemma-minus {l} {.(suc (suc (suc n)))} (SSS-mult n n₁) (SSS-mult .(n + l) m₁) = lemma-minus n₁ m₁

lemma-silly : ∀ {m n : ℕ} → Mult3 m → m ≡ n → Mult3 n
lemma-silly m eq rewrite eq = m

mult-imp-mult' : ∀ {n : ℕ} → Mult3 n → Mult3' n
mult-imp-mult' 0-mult = diff-mult zero 30 30 30-mult 30-mult refl
mult-imp-mult' (SSS-mult n M) = sum-mult 3 n silly3 (mult-imp-mult' M)

mult'-imp-mult : ∀ {n : ℕ} → Mult3' n → Mult3 n
mult'-imp-mult 30-mult = SSS-mult 27
                           (SSS-mult 24
                            (SSS-mult 21
                             (SSS-mult 18
                              (SSS-mult 15
                               (SSS-mult 12
                                (SSS-mult 9 (SSS-mult 6 (SSS-mult 3 (SSS-mult zero 0-mult)))))))))
mult'-imp-mult 21-mult = SSS-mult 18
                           (SSS-mult 15
                            (SSS-mult 12
                             (SSS-mult 9 (SSS-mult 6 (SSS-mult 3 (SSS-mult zero 0-mult))))))
mult'-imp-mult (sum-mult n m M M₁) = lemma-plus (mult'-imp-mult M) (mult'-imp-mult M₁)
mult'-imp-mult (diff-mult l n m M M₁ x) rewrite +-comm l n = lemma-minus {l} {n} (mult'-imp-mult M) (lemma-silly {m} {n + l} (mult'-imp-mult M₁) (sym x))
