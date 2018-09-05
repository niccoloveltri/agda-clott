module ManyClocks where

open import Data.Fin renaming (zero to fzero;suc to fsuc)
open import Data.Nat renaming (zero to Z;suc to S)
open import Level renaming (suc to lsuc)
open import Size

Clock : Set
Clock = Size

ClockCtx : ℕ → Set
ClockCtx n = Fin n → Clock

Tick : {n : ℕ} → ClockCtx n → Fin n → Set
Tick Δ i = Size< (Δ i)

TickCtx : {n : ℕ} (i : Fin n) (Δ : ClockCtx n) → Tick Δ i → ClockCtx n
TickCtx fzero Δ α fzero = α
TickCtx (fsuc i) Δ α fzero = Δ fzero
TickCtx fzero Δ α (fsuc x) = Δ (fsuc x)
TickCtx (fsuc i) Δ α (fsuc x) = α

record Ctx (ℓ : Level) (n : ℕ) : Set (lsuc ℓ) where
  constructor ctx
  field
    Γ : ClockCtx n → Set ℓ
    next : {Δ : ClockCtx n} (i : Fin n) {α : Tick Δ i} → Γ Δ → Γ (TickCtx i Δ α)
open Ctx

record ▻ {ℓ} {n : ℕ} (i : Fin n) (A : ClockCtx n → Set ℓ) (κ : ClockCtx n) : Set ℓ where
  coinductive
  field force : {α : Tick κ i} → A (TickCtx i κ α)
