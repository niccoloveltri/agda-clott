
module Presheaves where

open import Basics
open import Relation.Binary.PropositionalEquality
open import ClockContexts
open import Data.Nat
open import Size
open import Function

record PSh (n : ℕ) : Set₁ where
  field
    Obj : (Δ : ClockCtx n) → Set
    Mor : (Δ : ClockCtx n)(Δ' : ClockCtx≤ Δ)
      → Obj Δ → Obj Δ'
    MorId : {Δ : ClockCtx n} {x : Obj Δ}
      → Mor Δ (coeClockCtx Δ) x ≡ x 
    MorComp : {Δ : ClockCtx n}{Δ' : ClockCtx≤ Δ}
      → {Δ'' : ClockCtx≤ Δ'}{x : Obj Δ}
      → Mor Δ _ x ≡ Mor Δ' Δ'' (Mor Δ Δ' x)


