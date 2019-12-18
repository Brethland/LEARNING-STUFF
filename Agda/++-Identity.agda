{-# OPTIONS --safe #-}
{-# OPTIONS --sized-types #-}
module ++-Identity where

open import Size

-- +-identityʳ : ∀ (n : ℕ) → n + 0 ≅ n
-- +-identityʳ zero = refl
-- +-identityʳ (suc n) = cong suc (+-identityʳ n)

-- ∷-≅ : ∀ {m n : ℕ} {A : Set} (x : A) (xs : Vec A m) (ys : Vec A n) → m ≅ n → xs ≅ ys → (x ∷ xs) ≅ (x ∷ ys)
-- ∷-≅ x xs .xs refl refl = refl

-- ++-identityʳ : ∀ {n} {A : Set} (xs : Vec A n) → xs ++ [] ≅ xs
-- ++-identityʳ {.0} {A} [] = refl
-- ++-identityʳ {suc n} {A} (x ∷ xs)  = ∷-≅ x (xs ++ []) xs (+-identityʳ n) (++-identityʳ xs)

data Nat : {i : Size} -> Set where
  zero : {i : Size} -> Nat {↑ i}
  suc : {i : Size} -> Nat {i} -> Nat {↑ i}

sub : {i : Size} -> Nat {i} -> Nat {∞} -> Nat {i}
sub zero n = zero
sub (suc m) zero = suc m
sub (suc m) (suc n) = sub m n

div : {i : Size} -> Nat {i} -> Nat -> Nat {i}
div zero n = zero
div (suc m) n = suc (div (sub m n) n)
