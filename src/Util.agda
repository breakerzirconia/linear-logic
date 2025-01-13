module Util where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order.Recursive

Fin : ℕ → Type₀
Fin n = Σ[ k ∈ ℕ ] k < n
