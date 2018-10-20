{-
In this file, we define the product of presheaves.
It is defined pointwise.
-}
module Presheaves.Product where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves

module _ {n : ℕ} (P Q : PSh n) where

  private module P = PSh P
  private module Q = PSh Q

  -- Object part
  ProdObj : ClockCtx n → Set
  ProdObj Δ = P.Obj Δ × Q.Obj Δ

  -- Morphism part
  ProdMor : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
    → ProdObj Δ → ProdObj Δ'
  ProdMor Δ Δ' = map (P.Mor Δ Δ') (Q.Mor Δ Δ')

  -- Preservation of identity
  ProdMorId : {Δ : ClockCtx n} {x : ProdObj Δ}
    → ProdMor Δ (coeClockCtx Δ) x ≡ x
  ProdMorId = cong₂ _,_ P.MorId Q.MorId

  -- Preservation of composition
  ProdMorComp : {Δ : ClockCtx n} {Δ' : ClockCtx≤ Δ}
    → {Δ'' : ClockCtx≤ Δ'}{x : ProdObj Δ}
    → ProdMor Δ _ x ≡ ProdMor Δ' Δ'' (ProdMor Δ Δ' x)
  ProdMorComp = cong₂ _,_ P.MorComp Q.MorComp
  
  Prod : PSh n
  Prod = record
    { Obj = ProdObj
    ; Mor = ProdMor
    ; MorId = ProdMorId
    ; MorComp = ProdMorComp
    }
