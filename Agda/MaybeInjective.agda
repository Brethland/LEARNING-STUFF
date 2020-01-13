{-# OPTIONS --cubical --safe #-}
module MaybeInjective where

open import Data.Maybe
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Everything

-- maybe helpful
record Reveal_·_is_ {a b} {A : Set a} {B : A → Set b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set (ℓ-max a b) where
  constructor ⊢_⊣
  field eq : f x ≡ y

inspect : ∀ {a b} {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = ⊢ refl ⊣

-- prove it!
maybeInjective : {A B : Set} → Maybe A ≡ Maybe B → A ≡ B
maybeInjective = {!!}
