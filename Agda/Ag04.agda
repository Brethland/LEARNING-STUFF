module Ag04 where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

