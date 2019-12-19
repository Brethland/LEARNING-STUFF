module Ag10 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import Ag09 using (_≃_; _≲_; extensionality; _⇔_)
open Ag09.≃-Reasoning
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
import Function.Equivalence using (_⇔_)

⇔≃× : ∀ {A B : Set} → (A ⇔ B) ≃ ((A → B) × (B → A))
⇔≃× =
  record
  { to = λ{ x → ⟨ Ag09._⇔_.to x , Ag09._⇔_.from x ⟩}
  ; from = λ{ ⟨ x , y ⟩ → record { to = x ; from = y } }
  ; from∘to = λ{ x → refl }
  ; to∘from = λ{ x → refl }
  }

⊎-comm : ∀ {A B : Set} → (A ⊎ B) ≃ (B ⊎ A)
⊎-comm =
  record
  { to = λ{ (inj₁ x) → inj₂ x ; (inj₂ y) → inj₁ y }
  ; from =  λ{ (inj₁ x) → inj₂ x ; (inj₂ y) → inj₁ y}
  ; from∘to = λ{ (inj₁ x) → refl ; (inj₂ y) → refl }
  ; to∘from = λ{ (inj₁ x) → refl ; (inj₂ y) → refl}
  }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
  { to = λ{ (inj₁ (inj₁ x)) → inj₁ x ; (inj₁ (inj₂ y)) → inj₂ (inj₁ y) ; (inj₂ z) → inj₂ (inj₂ z) }
  ; from = λ{ (inj₁ x) → inj₁ (inj₁ x) ; (inj₂ (inj₁ y)) → inj₁ (inj₂ y) ; (inj₂ (inj₂ z)) → inj₂ z }
  ; from∘to = λ{ (inj₁ (inj₁ x)) → refl ; (inj₁ (inj₂ y)) → refl ; (inj₂ z) → refl }
  ; to∘from = λ{ (inj₁ x) → refl ; (inj₂ (inj₁ y)) → refl ; (inj₂ (inj₂ z)) → refl }
  }

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ = 
    record
    { to = λ{ (inj₂ a) → a }
    ; from = λ{ a → (inj₂ a) }
    ; from∘to = λ{ (inj₂ a) → refl }
    ; to∘from = λ{ a → refl }
    }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ {A} =
    ≃-begin
      (A ⊎ ⊥)
    ≃⟨ ⊎-comm ⟩
      (⊥ ⊎ A)
    ≃⟨ ⊥-identityˡ ⟩
      A
    ≃-∎
 
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , snd ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ y , snd ⟩ = inj₂ ⟨ y , snd ⟩

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ fst , snd ⟩) = ⟨ inj₁ fst , inj₁ snd ⟩
⊎×-implies-×⊎ (inj₂ ⟨ fst , snd ⟩) = ⟨ inj₂ fst , inj₂ snd ⟩

