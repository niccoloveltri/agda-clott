
module Later where

open import Types
open import Data.Nat
open import Data.Fin
open import Data.Product
open import ClockContexts
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
      (λ x → (α : Tick (Δ i)) (α' : Size≤ α)
        → A.Mor (Δ [ i ↦ α ]) {!!} (force x α)
          ≡
          force x α')

  Later : Ty n
  Later = record
    { Obj = {!!} --LaterObj
    ; Mor = {!!}
    ; MorId = {!!}
    ; MorComp = {!!}
    }
