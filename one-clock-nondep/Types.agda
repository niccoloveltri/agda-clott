module Types where

open import Clocks public

-- A type is a presheaf over clocks. 

record Ty ℓ : Set (lsuc ℓ) where
  constructor ty
  field
    A : Clock → Set ℓ
    next : (κ : Clock)(α : Tick= κ) → A κ → A α
    next-ass : (κ : Clock)(α : Tick= κ)(β : Tick= α)
      → (x : A κ) → next α β (next κ α x) ≡ next κ β x
    next-id : (κ : Clock) (x : A κ) → next κ κ x ≡ x

-- Terms.

record Tm ℓ (t : Ty ℓ) : Set ℓ where
  constructor tm
  open Ty t
  field
    τ : (κ : Clock) → A κ
    nextᵀᵐ : (κ : Clock) (α : Tick= κ) 
      → next κ α (τ κ) ≡ τ α  


{-

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
-}
