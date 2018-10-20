{-
Weakening of clock contexts.
From A : Ty n and a Name i we can make a type in Ty (S n).
We do this by leaving a position open, so we need i : Name (suc n).
-}
module CloTT.TypeFormers.WeakenClock where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure

module _ {n : ℕ} (A : Ty n) (i : Name (suc n)) where

  private module A = Ty A

  -- Object part
  WCObj : ClockCtx (suc n) → Set
  WCObj Δ = A.Obj (removeClock i Δ)

  -- Morphism part
  WCMor : (Δ : ClockCtx (suc n)) (Δ' : ClockCtx≤ Δ)
    → WCObj Δ → WCObj Δ'
  WCMor Δ Δ' x = A.Mor (removeClock i Δ) _ x

  -- Preservation of identity
  WCMorId : {Δ : ClockCtx (suc n)} {x : WCObj Δ}
    → WCMor Δ (coeClockCtx Δ) x ≡ x
  WCMorId = A.MorId

  -- Preservation of identity
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
