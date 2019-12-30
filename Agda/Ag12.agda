module Ag12 where

import Relation.Binary.PropositionalEquality as Eq
open Eq
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function
open import Ag09 hiding (_∘_)
-- open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open ≡-Reasoning
open ≃-Reasoning

postulate
  funExt : ∀ {m n : Level} {A : Set m} {B : Set n} {f g : A → B}
           → (∀ (x : A) → f x ≡ g x)
           → f ≡ g

lemma₀ : ∀ {A B : Set} → (a : A × B) → ⟨ proj₁ a , proj₂ a ⟩ ≡ a
lemma₀ ⟨ fst , snd ⟩ = refl

lemma₁ : ∀ {A : Set} {B C : A → Set}
         → (f : (x : A) → B x × C x)
         → (λ a → ⟨ proj₁ (f a) , proj₂ (f a) ⟩) ≡ f
lemma₁ f = refl

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× {A} {B} {C} =
  record
  { to      = λ bc → ⟨ proj₁ ∘ bc , proj₂ ∘ bc ⟩
  ; from    = λ bc a → ⟨ proj₁ bc a , proj₂ bc a ⟩
  ; from∘to = λ f → refl
  ; to∘from = λ f → refl
  }
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (_⊎_.inj₁ x₁) x = _⊎_.inj₁ (x₁ x)
⊎∀-implies-∀⊎ (_⊎_.inj₂ y) x = _⊎_.inj₂ (y x)

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
  { to = λ x → {!!}
  ; from = λ{ (inj₁ x) → ⟨ {!!} , {!!} ⟩ ; (inj₂ x) → {!!} }
  ; from∘to = {!!}
  ; to∘from = {!!}
  }
