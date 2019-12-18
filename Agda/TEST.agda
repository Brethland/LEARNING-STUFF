{-# OPTIONS --safe #-}
module TEST where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

arith-sum : ℕ → ℕ
arith-sum zero = zero
arith-sum (suc n) = suc n + arith-sum n

arith-formula : ℕ → ℕ
arith-formula n = ⌊ n * (n + 1) /2⌋

silly : ∀ (n m : ℕ) →  ⌊ n + n + m * (m + 1) /2⌋ ≡ n +  ⌊ m * (m + 1) /2⌋
silly zero m = refl
silly (suc n) m rewrite +-suc n n = cong suc (silly n m)

lemma : ∀ (n : ℕ) →  ⌊ suc n * (suc n + 1) /2⌋ ≡ suc n +  ⌊ n * (n + 1) /2⌋
lemma n rewrite *-comm n (suc n + 1) | +-assoc n 1 (n + (n + 1) * n) | *-comm (n + 1) n | +-comm n (suc (n + n * (n + 1)))
                                     | +-assoc n (n * (n + 1)) n | +-comm (n * (n + 1)) n | sym (silly n n) | +-assoc n n (n * (n + 1)) = refl
 
arith-eq : (n : ℕ) -> arith-formula n ≡ arith-sum n
arith-eq zero = refl
arith-eq (suc n) rewrite lemma n =  cong (_+_ (suc n)) (arith-eq n)
