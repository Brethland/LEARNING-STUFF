{-# OPTIONS --safe #-}
module tmp where

open import Relation.Nullary
open import Data.List public

data Suf {X : Set} : List X → List X → Set where
  sinit : ∀ l → Suf l l
  scons : ∀ x l l' → Suf l l' → Suf (x ∷ l) l'

lemma : ∀ {X} (x : X) l l' → Suf l (x ∷ l') → Suf l l'
lemma x .(x ∷ l') l' (sinit .(x ∷ l')) = scons x l' l' (sinit l')
lemma x .(x₁ ∷ l) l' (scons x₁ l .(x ∷ l') H) = scons x₁ l l' (lemma x l l' H)

less-is-not-more : ∀ {X} x (l : List X) → ¬ Suf l (x ∷ l)
less-is-not-more x [] = λ ()
less-is-not-more x (x₁ ∷ l) (scons .x₁ .l .(x ∷ x₁ ∷ l) H) = less-is-not-more x₁ l (lemma x l (x₁ ∷ l) H)


