module ProcessAlgebra where

open import Data.Nat
open import Data.Nat.Properties
open import Data.List

data Channel : Set where
  ℂ_ : ℕ → Channel

data ℙ : Set₁ where
  ν_[_] : List Channel → (Channel → ℙ) → ℙ
  B_,_ : Channel → ℙ → ℙ
  Send_[_],_ : ∀ {A : Set} → Channel → A → ℙ → ℙ
  Recv_,_ : ∀ {A : Set} → Channel → (A → ℙ) → ℙ
  _||_ : ℙ → ℙ → ℙ
  Dup_ : ℙ → ℙ
  Done : ℙ

data Message : Set₁ where
  _,_of_ : Channel → (A : Set) → A → Message

data Action : Set₁ where
  Out_ : Message → Action
  In_  : Message → Action

data Label : Set₁ where
  Silent : Label
  Act_ : Action → Label


