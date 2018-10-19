module WeakenClock where

--open import Presheaves
open import Types
open import Data.Nat
open import Data.Fin
open import Size
open import Basics
open import Data.Product
open import ClockContexts
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module _ {n : ℕ} (A : Ty n) (i : Fin (suc n)) where

  module A = Ty A

  WCObj : ClockCtx (suc n) → Set
  WCObj Δ = A.Obj (removeClock i Δ)

  WCMor : (Δ : ClockCtx (suc n)) (Δ' : ClockCtx≤ Δ)
        → WCObj Δ → WCObj Δ'
  WCMor Δ Δ' x = A.Mor (removeClock i Δ) _ x

  WCMorId : {Δ : ClockCtx (suc n)} {x : WCObj Δ}
          → WCMor Δ (coeClockCtx Δ) x ≡ x
  WCMorId = A.MorId

  WCMorComp : {Δ : ClockCtx (suc n)} {Δ' : ClockCtx≤ Δ}
              {Δ'' : ClockCtx≤ Δ'} {x : WCObj Δ}
            → WCMor Δ _ x ≡ WCMor Δ' Δ'' (WCMor Δ Δ' x)
  WCMorComp = A.MorComp

  WC : Ty (suc n)
  WC = record
    { Obj = WCObj
    ; Mor = WCMor
    ; MorId = WCMorId
    ; MorComp = WCMorComp
    }
