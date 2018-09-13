module Contexts where

open import Clocks public

-- A context (or a closed type) is a presheaf over clocks. Notice
-- though that clocks form a preorder, not a poset.

record Ctx ℓ : Set (lsuc ℓ) where
  constructor ctx
  field
    Γ : Clock → Set ℓ
    next : (κ : Clock)(α : Tick κ) → Γ κ → Γ α
    next-ass : (κ : Clock)(α : Tick κ)(β : Tick α)
      → (ρ : Γ κ) → next α β (next κ α ρ) ≡ next κ β ρ
--open Ctx public

ClTy = Ctx

-- A term in a closed type.

record ClTm ℓ (c : ClTy ℓ) : Set ℓ where
  constructor tm
  open Ctx c
  field
    τ : (κ : Clock) → Γ κ
    nextᵀᵐ : (κ : Clock) (α : Tick κ) 
      → next κ α (τ κ) ≡ τ α  -- : Γ c α


-- Empty context.

record ⊤ {ℓ} : Set ℓ where
  instance constructor tt

• : ∀ ℓ → Clock → Set ℓ
• ℓ _ = ⊤

next• : ∀ {ℓ} → (κ : Clock) (α : Tick κ) → • ℓ κ → • ℓ α
next• _ _ _ = tt

next•-ass : ∀{ℓ} → (κ : Clock) (α : Tick κ) (β : Tick α) (ρ : • ℓ κ)
  → next• α β (next• κ α ρ) ≡ next• κ β ρ
next•-ass _ _ _ _ = refl

Empty : ∀ ℓ → Ctx ℓ
Empty ℓ = ctx (• ℓ) next• next•-ass
