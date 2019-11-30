module Ag05 where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool

{-
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
-}
data Refine : (A : Set) → (A → Set) → Set where
  MkRefine : ∀ {A : Set} {f : A → Set} → (a : A) → (f a) → Refine A f

data _∧_ : Set → Set → Set where
  and : ∀ (A B : Set) → A ∧ B 

-- hl-suc : ∀ {a : Nat} → Refine Nat (λ )

silly : Set
silly = Refine Nat (_≡_ 0)

sillySon : silly
sillySon = MkRefine zero refl

data _≤_ : Nat → Nat → Set where
  z≤s : ∀ {b   : Nat} → 0 ≤ b
  s≤s : ∀ {m n : Nat} → m ≤ n → suc m ≤ suc n

data le-Total (x y : Nat) : Set where
  le-left  : x ≤ y → le-Total x y
  le-right : y ≤ x → le-Total x y

le : Nat → Nat → Bool
le zero    zero    = true
le zero    (suc n) = true
le (suc m) zero    = false
le (suc m) (suc n) = le m n

le-wtf : ∀ (x y : Nat) → le-Total x y
le-wtf zero    zero    = le-left z≤s
le-wtf zero    (suc y) = le-left z≤s
le-wtf (suc x) zero    = le-right z≤s
le-wtf (suc x) (suc y) with le-wtf x y
...                    | le-left  P = le-left  (s≤s P)
...                    | le-right Q = le-right (s≤s Q)
{- with le x y -- x ≤ y
...        | true  = {!!}
...        | false = {!!}
-}
_⟨_⟩ : (A : Set) → (A → Set) → Set
_⟨_⟩ = Refine

and-refine : ∀ {A : Set} (f g : A → Set)
           → (a : A) → f a → g a
           → Refine A (λ x → (f x) ∧ (g x))
and-refine f g x Pa Pb = MkRefine x (and (f x) (g x))

hSuc : ∀ {m : Nat} → ( Nat ⟨ (λ x → x ≤ m     ) ⟩ )
                   → ( Nat ⟨ (λ x → x ≤ suc m ) ⟩ )
hSuc (MkRefine a P) = MkRefine (suc a) (s≤s P)

postulate
  ≤-trans : ∀ {x y z : Nat} → x ≤ y → y ≤ z → x ≤ z

min : ∀ {m n : Nat} → ( Nat ⟨ (λ x → x ≤ m)             ⟩ )
                    → ( Nat ⟨ (λ x → x ≤ n)             ⟩ )
                    → ( Nat ⟨ (λ x → (x ≤ m) ∧ (x ≤ n)) ⟩ )
min (MkRefine a Pa) (MkRefine b Pb) with le-wtf a b
...                    {- a ≤ b -}  | le-left  P = {!and-refine ? ? Pa ? !}
...                    {- b ≤ a -}  | le-right Q = {!and-refine _ _ ? Pb !}
{- 
with le-Total a b
...                                 | le-left  a = {!!}
...                                 | le-right b = ? -}
{-
min {m} {n} (MkRefine a P₀) (MkRefine b P₁) with (le a b)
...                                 | true  = {!!}
...                                 | false = {!!}
-}
{-
min {m} {n} (MkRefine zero x)    (MkRefine b y)    = MkRefine 0 (and (zero ≤ m) (zero ≤ n))
min {m} {n} (MkRefine (suc a) x) (MkRefine zero y) = MkRefine 0 (and (zero ≤ m) (zero ≤ n))
min {suc m} {suc n} (MkRefine (suc a) x) (MkRefine (suc b) y) = {!hSuc (min (MkRefine a ?) (MkRefine b ?))!}
-}

