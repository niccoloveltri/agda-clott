module Terms where

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Basics
open import ClockContexts
open import Contexts
open import Types

module _ {n : ℕ} (Γ : Ctx n) (A : Ty n) where

  module Γ = Ctx Γ
  module A = Ty A

  Tm : Set
  Tm = Σ ((Δ : ClockCtx n) → Γ.Obj Δ → A.Obj Δ)
         (λ f → (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ) (x : Γ.Obj Δ)
              → A.Mor Δ Δ' (f Δ x) ≡ f Δ' (Γ.Mor Δ Δ' x))
