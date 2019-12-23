module Ag12 where

import Relation.Binary.PropositionalEquality as Eq
open Eq
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Ag09
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open ≡-Reasoning
open ≃-Reasoning

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× {A} {B} {C} =
  record
  { to = λ x → ⟨ (λ x₁ → proj₁ (x x₁)) , (λ x₁ → proj₂ (x x₁)) ⟩
  ; from = λ x y → ⟨ proj₁ x y , proj₂ x y ⟩
  ; from∘to = λ x₁ → {!!}
  ; to∘from = {!!}
  }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (_⊎_.inj₁ x₁) x = _⊎_.inj₁ (x₁ x)
⊎∀-implies-∀⊎ (_⊎_.inj₂ y) x = _⊎_.inj₂ (y x)

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

lemma : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
lemma {B} =
  record
  { to = λ z → ⟨ z aa , ⟨ z bb , z cc ⟩ ⟩
  ; from = λ P → λ{ aa → proj₁ P ; bb → proj₁ (proj₂ P) ; cc → proj₂ (proj₂ P)}
  ; from∘to = λ k → {!!}
  ; to∘from = λ z → {!!}
  }
