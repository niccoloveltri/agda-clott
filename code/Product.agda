module Product where

open import Data.Product
open import Data.Nat
open import ClockContexts
open import Presheaves
open import Relation.Binary.PropositionalEquality

module _ {n : ℕ} (P Q : PSh n) where

  module P = PSh P
  module Q = PSh Q
  
  ProdObj : ClockCtx n → Set
  ProdObj Δ = P.Obj Δ × Q.Obj Δ

  ProdMor : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
    → ProdObj Δ → ProdObj Δ'
  ProdMor Δ Δ' = map (P.Mor Δ Δ') (Q.Mor Δ Δ')

  ProdMorId : {Δ : ClockCtx n} {x : ProdObj Δ}
    → ProdMor Δ (coeClockCtx Δ) x ≡ x
  ProdMorId = cong₂ _,_ P.MorId Q.MorId

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
