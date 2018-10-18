
module Later where

open import Types
open import Data.Nat
open import Data.Fin
open import Data.Fin.Properties
open import Data.Product
open import ClockContexts
open import Size
open import Relation.Binary.PropositionalEquality

module _ {n : ℕ} (A : Ty n) (i : Fin n) where

  module A = Ty A

  record ▻ (Δ : ClockCtx n) : Set where
    coinductive
    field
      force : (α : TickCtx Δ i) → A.Obj (Δ [ i ↦ α ])
  open ▻

  LaterObj : (Δ : ClockCtx n) → Set
  LaterObj Δ =
    Σ (▻ Δ)
      (λ x → (α : Tick (Δ i)) (α' : Size≤ ((Δ [ i ↦ α ]) i))
        → A.Mor (Δ [ i ↦ α ]) ((Δ [ i ↦ α ]) [ i ↦ α' ]≤) (force x α)
          ≡
          subst A.Obj {!!} (force x {!!}))
{-
      (λ x → (α : Tick (Δ i)) (α' : Size≤ α)
        → A.Mor (Δ [ i ↦ α ]) ((Δ [ i ↦ α ])
                [ i ↦ subst Size≤ (sym (id[↦] {Δ = Δ}{i}{α})) α' ]≤) (force x α)
          ≡
          subst A.Obj {!!} (force x (transSize< {Δ i}{α} α' ))) 
-}


  Later : Ty n
  Later = record
    { Obj = {!!} --LaterObj
    ; Mor = {!!}
    ; MorId = {!!}
    ; MorComp = {!!}
    }
