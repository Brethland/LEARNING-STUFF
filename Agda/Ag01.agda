module Ag01 where

-- open import Agda.Builtin.Nat


data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

