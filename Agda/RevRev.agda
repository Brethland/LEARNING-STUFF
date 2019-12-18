{-# OPTIONS --safe #-}
module RevRev where

open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.List.Properties

rev : ∀ {ℓ} {A : Set ℓ} → List A → List A
rev [] = []
rev (x ∷ xs) = rev xs ++ x ∷ []

lemma : ∀ {ℓ} {A : Set ℓ} (a b : List A) → rev (a ++ b) ≡ rev b ++ rev a
lemma [] b rewrite ++-identityʳ (rev b) = refl
lemma (x ∷ a) b rewrite lemma a b | ++-assoc (rev b) (rev a) (x ∷ []) = refl

revrevid : ∀ {ℓ} {A : Set ℓ} (a : List A) → rev (rev a) ≡ a
revrevid [] = refl
revrevid (x ∷ a) rewrite lemma (rev a) (x ∷ []) | revrevid a = refl
