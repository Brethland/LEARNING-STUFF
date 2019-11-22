module Ag05 where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

{-
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
-}
data Refine : (A : Set) → (A → Set) → Set where
  MkRefine : ∀ {A : Set} {f : A → Set} → (a : A) → (f a) → Refine A f

silly : Set
silly = Refine Nat (_≡_ 0)

sillySon : silly
sillySon = MkRefine zero refl



