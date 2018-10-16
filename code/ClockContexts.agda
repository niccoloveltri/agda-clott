module ClockContexts where

open import Basics
open import Size
open import Data.Fin
open import Data.Nat hiding (_≟_)
open import Data.Vec
open import Function
open import Data.Product
open import Data.Fin.Properties
open import Relation.Nullary

Clock = Size

Size≤ : Size → Set
Size≤ i = Size< (↑ i)

coeSize : (i : Size) → Size≤ i
coeSize i = i

ClockCtx : ℕ → Set
ClockCtx n = Fin n → Clock

ClockCtx< : {n : ℕ} → ClockCtx n → Set
ClockCtx< {n} Δ = Σ (Fin n) (λ i → Size< (Δ i))

ClockCtx≤ : {n : ℕ} → ClockCtx n → Set
ClockCtx≤ {n} Δ = (i : Fin n) → Size≤ (Δ i)

coeClockCtx : {n : ℕ} (Δ : ClockCtx n) → ClockCtx≤ Δ
coeClockCtx Δ i = coeSize (Δ i)

Tick : Size → Set
Tick i = Size< i

TickCtx : {n : ℕ} → ClockCtx n → Fin n → Set
TickCtx Δ j = Tick (Δ j)

remove : ∀{n} → Fin (suc n) → ClockCtx (suc n) → ClockCtx n
remove zero Δ j = Δ (suc j)
remove (suc i) Δ zero = Δ zero
remove (suc i) Δ (suc j) = remove i (Δ ∘ suc) j

_[_↦_] : {n : ℕ} → ClockCtx n → Fin n → Clock → ClockCtx n
(Δ [ i ↦ κ ]) j =
  case (i ≟ j) of (λ { (yes p) → κ ; (no ¬p) → Δ j })

