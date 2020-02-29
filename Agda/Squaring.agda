{-# OPTIONS --safe #-}
module Squaring where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Product
open import Data.Bool hiding (_≤_;_<_)
open import Data.Nat.Properties

open ≡-Reasoning

div-mod2 : ℕ → ℕ × Bool
div-mod2 0 = 0 , false
div-mod2 (suc 0) = 0 , true
div-mod2 (suc (suc n)) = let q , r = div-mod2 n in suc q , r

-- The first argument (k) helps Agda to prove
-- that the function terminates
pow-sqr-aux : ℕ → ℕ → ℕ → ℕ
pow-sqr-aux 0 _ _ = 1
pow-sqr-aux _ _ 0 = 1
pow-sqr-aux (suc k) b e with div-mod2 e
... | e' , false = pow-sqr-aux k (b * b) e'
... | e' , true = b * pow-sqr-aux k (b * b) e'

pow-sqr : ℕ → ℕ → ℕ
pow-sqr b e = pow-sqr-aux e b e

div-mod2-spec : ∀ n → let q , r = div-mod2 n in 2 * q + (if r then 1 else 0) ≡ n
div-mod2-spec 0 = refl
div-mod2-spec 1 = refl
div-mod2-spec (suc (suc n)) with div-mod2 n | div-mod2-spec n
... | q , r | eq rewrite +-suc q (q + 0) | eq = refl

div-mod2-lt : ∀ n → 0 < n → proj₁ (div-mod2 n) < n
div-mod2-lt 0 lt = lt
div-mod2-lt 1 lt = lt
div-mod2-lt 2 lt = s≤s (s≤s z≤n)
div-mod2-lt (suc (suc (suc n))) lt with
  div-mod2 (suc n) | div-mod2-lt (suc n) (s≤s z≤n)
... | q , r | ih = ≤-step (s≤s ih)

pow-lemma : ∀ b e → (b * b) ^ e ≡ b ^ (2 * e)
pow-lemma b e = begin
  (b * b) ^ e ≡⟨ cong (λ t → (b * t) ^ e) (sym (*-identityʳ b)) ⟩
  (b ^ 2) ^ e ≡⟨ ^-*-assoc b 2 e ⟩
  b ^ (2 * e) ∎

pow-sqr-lemma : ∀ k b e → e ≤ k → pow-sqr-aux k b e ≡ b ^ e
pow-sqr-lemma 0 _ 0 _ = refl
pow-sqr-lemma (suc k) _ 0 _ = refl
pow-sqr-lemma (suc k) b (suc e) (s≤s le) with
  div-mod2 (suc e) | div-mod2-spec (suc e) | div-mod2-lt (suc e) (s≤s z≤n)
... | e' , false | eq | lt = begin
  pow-sqr-aux k (b * b) e' ≡⟨ pow-sqr-lemma k (b * b) e' (≤-trans (≤-pred lt) le) ⟩
  (b * b) ^ e' ≡⟨ pow-lemma b e' ⟩
  b ^ (2 * e') ≡⟨ cong (b ^_) (trans (sym (+-identityʳ (e' + (e' + 0)))) eq) ⟩
  b ^ suc e ∎
... | e' , true | eq | lt = cong (b *_) (begin
  pow-sqr-aux k (b * b) e' ≡⟨ pow-sqr-lemma k (b * b) e' (≤-trans (≤-pred lt) le) ⟩
  (b * b) ^ e' ≡⟨ pow-lemma b e' ⟩
  b ^ (2 * e') ≡⟨ cong (b ^_) (suc-injective (trans (+-comm 1 _) eq)) ⟩
  b ^ e ∎)

