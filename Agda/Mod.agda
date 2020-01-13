{-# OPTIONS --safe #-}
module Mod where

open import Data.Fin
open import Data.Nat as ℕ
  using (ℕ; zero; suc; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality
open import Function

private variable k : ℕ

last : Fin (suc k)
last {k = zero} = zero
last {k = suc _} = suc last

negate : Fin k -> Fin k
negate zero = zero
negate (suc zero) = last
negate (suc (suc n)) = inject₁ (negate (suc n))

subt : Fin k -> Fin k -> Fin k
subt n zero = n
subt zero (suc m) = negate (suc m)
subt (suc n) (suc m) with (compare n m)
...| less _ _ = suc (subt n m)
...| _ = inject₁ (subt n m)

add : Fin k -> Fin k -> Fin k
add n m = subt n (negate m)

multAux : ∀{n} → ℕ → (Fin n → Fin n) → Fin n → Fin n
multAux zero _ x = x
multAux (suc n) f x = multAux n f (f x)

mult : Fin k -> Fin k -> Fin k
mult zero m = zero
mult (suc n) m = multAux (toℕ n) (add m) zero

zer : Fin 5
zer = zero
one : Fin 5
one = suc zero
two : Fin 5
two = suc (suc zero)
three : Fin 5
three = suc (suc (suc zero))
four : Fin 5
four = suc (suc (suc (suc zero)))
