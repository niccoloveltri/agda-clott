module Sum where

open import Data.Sum
open import Data.Nat
open import ClockContexts
open import Presheaves
open import Relation.Binary.PropositionalEquality

module _ {n : ℕ} (P Q : PSh n) where

  module P = PSh P
  module Q = PSh Q
  
  SumObj : ClockCtx n → Set
  SumObj Δ = P.Obj Δ ⊎ Q.Obj Δ

  SumMor : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
    → SumObj Δ → SumObj Δ'
  SumMor Δ Δ' = map (P.Mor Δ Δ') (Q.Mor Δ Δ')

  SumMorId : {Δ : ClockCtx n} {x : SumObj Δ}
    → SumMor Δ (coeClockCtx Δ) x ≡ x
  SumMorId {x = inj₁ p} = cong inj₁ P.MorId
  SumMorId {x = inj₂ q} = cong inj₂ Q.MorId

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
