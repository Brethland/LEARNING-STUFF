module Ag09 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

-- exercises

≃-implies-≲ : ∀ {A B : Set}
  → A ≃ B
  -----
  → A ≲ B

≃-implies-≲ A≃B =
  record
  { to = to A≃B
  ; from = from A≃B
  ; from∘to = from∘to A≃B
  }

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_

⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl =
  record
  { to = λ{x → x}
  ; from = λ{y → y}
  }

⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym A⇔B =
  record
    { to   = from A⇔B
    ; from = to A⇔B
    }

⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans A⇔B B⇔C =
  record
  { to = to B⇔C ∘ to A⇔B
  ; from = from A⇔B ∘ from B⇔C
  }

