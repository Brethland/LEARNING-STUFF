module Ag03 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm; +-suc)

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
  → m ≤ n

inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
  → m ≡ zero

inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {0} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ } → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where
  forward :
    m ≤ n → Total m n
  flipped :
    n ≤ m → Total m n

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-mono-ʳ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-mono-ʳ 0 _ _ p≤q = z≤n
*-mono-ʳ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-mono-ʳ n p q p≤q)

*-mono-ˡ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-mono-ˡ m n p m≤n rewrite *-comm m p | *-comm n p = *-mono-ʳ p m n m≤n

*-mono : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono m n p q m≤n p≤q = ≤-trans (*-mono-ˡ m n p m≤n) (*-mono-ʳ n p q p≤q)

infix 4 _⟨_

data _⟨_ : ℕ → ℕ → Set where
  z⟨s : ∀ {n : ℕ} → 0 ⟨ suc n
  s⟨s : ∀ {m n : ℕ} → m ⟨ n → suc m ⟨ suc n

⟨-trans : ∀ {m n p : ℕ} → m ⟨ n → n ⟨ p → m ⟨ p
⟨-trans z⟨s (s⟨s n⟨p) = z⟨s
⟨-trans (s⟨s m⟨n) (s⟨s n⟨p) = s⟨s (⟨-trans m⟨n n⟨p)

data Total-trichotomy (m n : ℕ) : Set where
  lt : m ⟨ n → Total-trichotomy m n
  eq : m ≡ n → Total-trichotomy m n
  gt : n ⟨ m → Total-trichotomy m n

trichotomy : ∀ (m n : ℕ) → Total-trichotomy m n
trichotomy zero zero = eq refl
trichotomy zero (suc n) = lt z⟨s
trichotomy (suc m) zero = gt z⟨s
trichotomy (suc m) (suc n) with trichotomy m n
...                          | lt m⟨n = lt (s⟨s m⟨n)
...                          | eq m≡n = eq (cong suc m≡n)
...                          | gt n⟨m = gt (s⟨s n⟨m)

+-monoʳ-⟨ : ∀ (n p q : ℕ) → p ⟨ q → n + p ⟨ n + q
+-monoʳ-⟨ 0 _ _ p⟨q = p⟨q
+-monoʳ-⟨ (suc n) p q p⟨q = s⟨s (+-monoʳ-⟨ n p q p⟨q)

+-monoˡ-⟨ : ∀ (m n p : ℕ) → m ⟨ n → m + p ⟨ n + p
+-monoˡ-⟨ m n p m⟨n rewrite +-comm m p | +-comm n p = +-monoʳ-⟨ p m n m⟨n

+-mono-⟨ : ∀ (m n p q : ℕ) → m ⟨ n → p ⟨ q → m + p ⟨ n + q
+-mono-⟨ m n p q m⟨n p⟨q = ⟨-trans (+-monoˡ-⟨ m n p m⟨n) (+-monoʳ-⟨ n p q p⟨q)

≤-iffˡ-⟨ : ∀ (m n : ℕ) → suc m ≤ n → m ⟨ n
≤-iffˡ-⟨ 0 _ (s≤s z≤n) = z⟨s
≤-iffˡ-⟨ (suc m) (suc n) (s≤s sm≤n) = s⟨s (≤-iffˡ-⟨ m n sm≤n)

≤-iffʳ-⟨ : ∀ (m n : ℕ) → m ⟨ n → suc m ≤ n
≤-iffʳ-⟨ .0 .(suc _) z⟨s = s≤s z≤n
≤-iffʳ-⟨ .(suc _) .(suc _) (s⟨s m⟨n) = s≤s (≤-iffʳ-⟨ _ _ m⟨n)

data Even : ℕ → Set
data Odd  : ℕ → Set

data Even where

  zero :
      ---------
      Even zero

  suc  : ∀ {n : ℕ}
    → Odd n
      ------------
    → Even (suc n)

data Odd where

  suc   : ∀ {n : ℕ}
    → Even n
      -----------
    → Odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → Even m
  → Even n
    ------------
  → Even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → Odd m
  → Even n
    -----------
  → Odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)

o+o≡e : ∀ {m n : ℕ} → Odd m → Odd n → Even (m + n)
o+o≡e {m} {suc n} om (suc en) rewrite +-suc m n = suc (o+e≡o om en)

e+o≡o : ∀ (m n : ℕ) → Even m → Odd n → Odd(m + n)
e+o≡o .0 .(suc _) zero (suc x) = suc x
e+o≡o (suc m) (suc n) (suc x) (suc x₁) rewrite +-suc m n = suc (suc (o+e≡o x x₁))

infixl 7 _e*e_ _o*e_ _o*o_ _e*o_
_e*e_ : ∀ {m n : ℕ} → Even m → Even n → Even (m * n)
_o*e_ : ∀ {m n : ℕ} → Odd  m → Even n → Even (m * n)
_o*o_ : ∀ {m n : ℕ} → Odd  m → Odd  n → Odd  (m * n)
_e*o_ : ∀ {m n : ℕ} → Even m → Odd  n → Even (m * n)

zero e*e en  = zero
suc x e*e en = e+e≡e en (x o*e en)

suc x o*e en = e+e≡e en (x e*e en)

suc x o*o on = o+e≡o on (x e*o on)

zero e*o on  = zero
suc x e*o on = o+o≡e on (x o*o on)
