{-# OPTIONS --safe #-}
module Sol01 where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

fibAux : ℕ -> ℕ -> ℕ -> ℕ
fibAux a b 0 = a
fibAux a b (suc n) = fibAux b (a + b) n

fib2 : ℕ -> ℕ
fib2 = fibAux 0 1

fib : ℕ -> ℕ
fib 0 = 0
fib 1 = 1
fib (suc (suc n)) = fib (suc n) + fib n

lemma : ∀ (a b c d n : ℕ) → fibAux (a + c) (b + d) n ≡ fibAux a b n + fibAux c d n
lemma a b c d zero = refl
lemma a b c d (suc n) rewrite sym (+-assoc (a + c) b d) | +-assoc a c b | +-comm c b | sym (+-assoc a b c) | +-assoc (a + b) c d = lemma b (a + b) d (c + d) n

fibEq : (n : ℕ) -> fib2 n ≡ fib n
fibEq zero = refl
fibEq (suc zero) = refl
fibEq (suc (suc n)) rewrite lemma 0 1 1 1 n | fibEq n | fibEq (suc n) | +-comm (fib n) (fib (suc n)) = refl
