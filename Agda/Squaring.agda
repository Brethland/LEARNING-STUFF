{-# OPTIONS --safe #-}
module Squaring where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Product
open import Data.Bool
open import Data.Nat.Properties

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

pow-eq : ∀ b e → pow-sqr b e ≡ b ^ e
pow-eq b zero = refl
pow-eq b (suc e) with div-mod2 e
... | e' , false = {!!}
... | e' , true  = {!cong (b *_) (pow-eq b (e' * 2))!}


