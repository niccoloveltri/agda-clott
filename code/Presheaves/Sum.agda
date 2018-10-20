{-
In this file, we define the sum of presheaves.
It is defined pointwise.
-}
module Presheaves.Sum where

open import Data.Sum
open import Prelude
open import Presheaves.Presheaves

module _ {n : ℕ} (P Q : PSh n) where

  private module P = PSh P
  private module Q = PSh Q

  -- Object part
  SumObj : ClockCtx n → Set
  SumObj Δ = P.Obj Δ ⊎ Q.Obj Δ

  -- Morphism part
  SumMor : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
    → SumObj Δ → SumObj Δ'
  SumMor Δ Δ' = map (P.Mor Δ Δ') (Q.Mor Δ Δ')

  -- Preservation of identity
  SumMorId : {Δ : ClockCtx n} {x : SumObj Δ}
    → SumMor Δ (coeClockCtx Δ) x ≡ x
  SumMorId {x = inj₁ p} = cong inj₁ P.MorId
  SumMorId {x = inj₂ q} = cong inj₂ Q.MorId

  -- Preservation of composition
  SumMorComp : {Δ : ClockCtx n} {Δ' : ClockCtx≤ Δ}
    → {Δ'' : ClockCtx≤ Δ'}{x : SumObj Δ}
    → SumMor Δ _ x ≡ SumMor Δ' Δ'' (SumMor Δ Δ' x)
  SumMorComp {x = inj₁ p} = cong inj₁ P.MorComp
  SumMorComp {x = inj₂ q} = cong inj₂ Q.MorComp
  
  Sum : PSh n
  Sum = record
    { Obj = SumObj
    ; Mor = SumMor
    ; MorId = SumMorId
    ; MorComp = λ {_}{_}{_}{x} → SumMorComp {x = x}
    }
