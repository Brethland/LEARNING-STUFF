module gugugu where

open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.List.Properties
open import Agda.Builtin.Sigma
-- you can import other functions from the stdlib here

++-injectiveʳ : ∀ {ℓ} {A : Set ℓ} (a b c : List A) → a ++ b ≡ a ++ c → b ≡ c
++-injectiveʳ [] b c p = p
++-injectiveʳ (x ∷ a) b c p = ++-injectiveʳ a b c (snd (∷-injective p))

lemma : ∀ {ℓ} {A : Set ℓ} (x : A) (xs ys : List A) → xs ++ x ∷ ys ≡ (xs ++ x ∷ []) ++ ys
lemma x [] ys = refl
lemma x (x₁ ∷ xs) ys = cong (_∷_ x₁) (lemma x xs ys)

col : ∀ {ℓ} {A : Set ℓ} (x : A) (xs : List A) → xs ++ x ∷ [] ≡ (xs ∷ʳ x)
col x [] = refl
col x (x₁ ∷ xs) = refl

silly' : ∀ {ℓ} {A : Set ℓ} (x : A) (xs ys : List A) → xs ++ x ∷ [] ≡ ys ++ x ∷ [] → xs ∷ʳ x ≡ ys ∷ʳ x
silly' x xs ys = λ z → z

silly : ∀ {ℓ} {A : Set ℓ} (x : A) (xs ys : List A) → xs ++ x ∷ [] ≡ ys ++ x ∷ [] → xs ≡ ys
silly x xs ys p rewrite col x xs | col x ys = fst (∷ʳ-injective xs ys (silly' x xs ys p))

-- inductive can do this job too.
++-injectiveˡ : ∀ {ℓ} {A : Set ℓ} (a b c : List A) → a ++ c ≡ b ++ c → a ≡ b
++-injectiveˡ a b [] p rewrite ++-identityʳ a | ++-identityʳ b = p
++-injectiveˡ a b (x ∷ c) p rewrite lemma x a c | lemma x b c = silly x a b (++-injectiveˡ (a ++ x ∷ []) (b ++ x ∷ []) c p)
