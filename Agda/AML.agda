module AML where

open import Level
open import Data.Product

data satisfied (a : Set) (m : Set → Set) : Set where
  s : m a → satisfied a m

data reachability (m₀ : Set → Set) (m : Set → Set) : Set where
  tt : reachability m₀ m

data necessarity (m₀ : Set → Set) (a : Set) : Set₁ where
  n : ∀ m → (reachability m₀ m) → satisfied a m → necessarity m₀ a

□_ : Set → Set₁
□_ = necessarity {!!}

data posibility (m₀ : Set → Set) (a : Set) : Set₁ where
  p : ∃[ m ](reachability m₀ m → satisfied a m) → posibility m₀ a

◇_ : Set → Set₁
◇_ = posibility {!!}
