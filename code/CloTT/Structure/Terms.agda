{-
A Term is a natural transformation.
-}
module CloTT.Structure.Terms where

open import Data.Product
open import Prelude
open import CloTT.Structure.Contexts
open import CloTT.Structure.Types

module _ {n : ℕ} (Γ : Ctx n) (A : Ty n) where

  private module Γ = Ctx Γ
  private module A = Ty A

  Tm : Set
  Tm = Σ ((Δ : ClockCtx n) → Γ.Obj Δ → A.Obj Δ)
         (λ f → (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ) (x : Γ.Obj Δ)
              → A.Mor Δ Δ' (f Δ x) ≡ f Δ' (Γ.Mor Δ Δ' x))
