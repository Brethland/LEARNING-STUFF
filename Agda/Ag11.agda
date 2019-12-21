module Ag11 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import Ag09 using (_≃_; extensionality)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contraposition)
open import Ag03 using (_⟨_)

⟨-irreflexive : ∀ (n : ℕ) → ¬ (n ⟨ n)
⟨-irreflexive (suc n) (_⟨_.s⟨s H) = ⟨-irreflexive n H

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× =
  record
  { to = λ z → (λ x → z (inj₁ x)) Data.Product., (λ x → z (inj₂ x))
  ; from = λ{ (fst Data.Product., snd) → λ {(inj₁ x) → fst x; (inj₂ y) → snd y} }
  ; from∘to = λ x → extensionality λ { (inj₁ y) → refl ; (inj₂ z) → refl }
  ; to∘from = λ {(fst Data.Product., snd) → refl}
  }

-- ×-dual-⊎ : ∀ {A B : Set} → ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
-- ×-dual-⊎ =
--  record
--  { to = λ x → inj₁ λ y → {!!} 
--  ; from = λ { (inj₁ x) → λ z → x (Data.Product.proj₁ z) ; (inj₂ y) → λ z → y (Data.Product.proj₂ z)}
--  ; from∘to = {!!}
--  ; to∘from = {!!}
--  }

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ (λ x → k (inj₁ x)))

postulate
  dne : ∀ {A : Set} → ¬ ¬ A → A

em-dne : ∀ {A : Set} → (A ⊎ ¬ A) → (¬ ¬ A → A)
em-dne (inj₁ x) ¬¬A = x
em-dne (inj₂ y) ¬¬A = ⊥-elim (¬¬A y)

dne-em : (∀ (A : Set) → ¬ ¬ A → A) → (∀ (A : Set) → A ⊎ ¬ A)
dne-em H = λ a → H (a ⊎ ((x : a) → ⊥)) (λ z → z (inj₂ (λ x → z (inj₁ x))))
