module Solution where

open import Data.List
open import Data.Nat
open import Data.Bool hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data Subseq : List ℕ → List ℕ → Set where
  subseq-nil  :                            Subseq [] []
  subseq-take : ∀ a xs ys → Subseq xs ys → Subseq (a ∷ xs) (a ∷ ys)
  subseq-drop : ∀ a xs ys → Subseq xs ys → Subseq xs (a ∷ ys)

_⊂_ : List ℕ → List ℕ → Set
_⊂_ = Subseq

subseq-match : (xs ys : List ℕ) → Bool
subseq-match [] ys = true
subseq-match (x ∷ xs) [] = false
subseq-match (x ∷ xs) (y ∷ ys) with x ≟ y
... | yes _ = subseq-match xs ys
... | no  _ = subseq-match (x ∷ xs) ys

_⊂*_ : List ℕ → List ℕ → Bool
_⊂*_ = subseq-match

-- silly : ∀ (a : ℕ) (xs ys : List ℕ) → xs ⊂* ys ≡ (a ∷ xs) ⊂* (a ∷ ys)
-- silly a xs ys = ?

subseq-match⇒subseq : ∀ xs ys → xs ⊂* ys ≡ true → xs ⊂ ys
subseq-match⇒subseq []       []       H = subseq-nil
subseq-match⇒subseq []       (y ∷ ys) H = subseq-drop y [] ys (subseq-match⇒subseq [] ys H)
subseq-match⇒subseq (x ∷ xs) (y ∷ ys) H with x ≟ y
... | yes P rewrite sym P = subseq-take x xs ys (subseq-match⇒subseq xs ys H)
... | no  _               = subseq-drop y (x ∷ xs) ys (subseq-match⇒subseq (x ∷ xs) ys H)

subseq⇒subseq-match : ∀ xs ys → xs ⊂ ys → xs ⊂* ys ≡ true
subseq⇒subseq-match .[] .[] subseq-nil = refl
subseq⇒subseq-match .(a ∷ xs) .(a ∷ ys) (subseq-take a xs ys H) rewrite subseq⇒subseq-match xs ys H = {!!}
subseq⇒subseq-match xs .(a ∷ ys) (subseq-drop a .xs ys H) = {!!}
