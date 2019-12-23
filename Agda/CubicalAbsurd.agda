{-# OPTIONS --cubical --safe #-}
module CubicalAbsurd where

open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Empty

theWrongThing : 1 + 1 ≡ 3 → ⊥
theWrongThing thatMoney = {!!}
