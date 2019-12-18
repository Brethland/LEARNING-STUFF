module gugugu where

open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.List.Properties
open import Agda.Builtin.Sigma
-- you can import other functions from the stdlib here

++-injectiveʳ : ∀ {ℓ} {A : Set ℓ} (a b c : List A) → a ++ b ≡ a ++ c → b ≡ c
++-injectiveʳ [] b c p = p
++-injectiveʳ (x ∷ a) b c p = ++-injectiveʳ a b c (snd (∷-injective p))

-- pretty hard
-- try to use cong to convert to an eazier problem

lemma : ∀ {ℓ} {A : Set ℓ} (x : A) (xs ys : List A) → xs ++ x ∷ ys ≡ (xs ++ x ∷ []) ++ ys
lemma x [] ys = refl
lemma x (x₁ ∷ xs) ys = cong (_∷_ x₁) (lemma x xs ys)

silly : ∀ {ℓ} {A : Set ℓ} (x : A) (xs ys : List A) → xs ++ x ∷ [] ≡ ys ++ x ∷ [] → xs ≡ ys
silly x xs ys p = {!!}

++-injectiveˡ : ∀ {ℓ} {A : Set ℓ} (a b c : List A) → a ++ c ≡ b ++ c → a ≡ b
++-injectiveˡ a b [] p rewrite ++-identityʳ a | ++-identityʳ b = p
++-injectiveˡ a b (x ∷ c) p rewrite lemma x a c | lemma x b c = silly x a b (++-injectiveˡ (a ++ x ∷ []) (b ++ x ∷ []) c p)
 
