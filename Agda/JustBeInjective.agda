{-# OPTIONS --cubical --safe #-}
module JustBeInjective where

open import Cubical.Core.Everything
open import Cubical.Data.Unit
data maybe (A : Set) : Set where
  just : A -> maybe A
  nothing : maybe A

variable A : Set

unwrap : A → (a : maybe A) → A
unwrap _ (just x) = x
unwrap a nothing = a

just-injective : ∀ {A : Set} (a b : A) → just a ≡ just b → a ≡ b
just-injective a b p i = unwrap a (p i)
