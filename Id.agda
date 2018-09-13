module Id where

open import Clocks
open import Contexts
open import Types
open import Pi

Id : ∀{ℓ} (c : ClTy ℓ)
  → (x y : ClTm ℓ c) → Clock → Set ℓ
Id (ctx A nA aA) (tm x nx) (tm y ny) κ = x κ ≡ y κ  

nextId : ∀{ℓ} (c : ClTy ℓ)
  → (x y : ClTm ℓ c)
  → (κ : Clock) (α : Tick κ)
  → ClTm.τ x κ ≡ ClTm.τ y κ → ClTm.τ x α ≡ ClTm.τ y α
nextId (ctx A nA aA) (tm x nx) (tm y ny) κ α p =
  trans (sym (nx κ α)) (trans (cong (nA κ α) p) (ny κ α))

nextId-ass : ∀{ℓ} (c : ClTy ℓ)
  → (x y : ClTm ℓ c)
  → (κ : Clock) (α : Tick κ) (β : Tick α) (ρ : Id c x y κ)
  → nextId c x y α β (nextId c x y κ α ρ) ≡ nextId c x y κ β ρ
nextId-ass c x y κ α β ρ = uip

Idᵀʸ : ∀{ℓ} (c : ClTy ℓ)
  → (x y : ClTm ℓ c) → ClTy ℓ
Idᵀʸ c x y = ctx (Id c x y) (nextId c x y) (nextId-ass c x y)

syntax Idᵀʸ c x y = x ≡[ c ] y 

toId : ∀{ℓ} {c : ClTy ℓ}
  → {x y : ClTm ℓ c}
  → ((κ : Clock) → Ctx.Γ (Idᵀʸ c x y) κ)
  → ClTm ℓ (x ≡[ c ] y)
toId p = tm p r
  where
    r : ∀ κ α → _
    r _ _ = uip
