module Types where

open import Contexts public

PathOver : ∀{ℓ ℓ'} {A : Set ℓ} (B : A → Set ℓ')
  → {a a' : A} (p : a ≡ a')
  → (b : B a) (b' : B a') → Set ℓ'
PathOver B refl b b' = b ≡ b'

infix 30 PathOver
syntax PathOver B p u v =
  u ≡ v [ B ↓ p ]

↓-cst-in : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}
  → {x y : A} {p : x ≡ y} {u v : B}
  → u ≡ v
  → u ≡ v [ (λ _ → B) ↓ p ]
↓-cst-in {p = refl} q = q

-- Dependent types. As usual in presheaf semantics, a type in a
-- context Γ is a presheaf on the category of elements of Γ.

record Ty {ℓ} ℓ' (c : Ctx ℓ) : Set (lsuc (ℓ' ⊔ ℓ)) where
  constructor ty
  open Ctx c
  field
    A : (κ : Clock) → Γ κ → Set ℓ'
    nextᵀʸ : (κ : Clock)(α : Tick κ)(ρ : Γ κ) → A κ ρ → A α (next κ α ρ)
    nextᵀʸ-ass : (κ : Clock)(α : Tick κ)(β : Tick α)
      → (ρ : Γ κ)(x : A κ ρ)
      → nextᵀʸ α β (next κ α ρ) (nextᵀʸ κ α ρ x) ≡ nextᵀʸ κ β ρ x  [ A β ↓ next-ass κ α β ρ ]
--open Ty public


-- Terms.

record Tm ℓ (c : Ctx ℓ)(t : Ty ℓ c) : Set ℓ where
  constructor tm
  open Ctx c
  open Ty t
  field
    τ : (κ : Clock) (ρ : Γ κ) → A κ ρ
    nextᵀᵐ : (κ : Clock) (α : Tick κ) (ρ : Γ κ)
      → nextᵀʸ κ α ρ (τ κ ρ) ≡ τ α (next κ α ρ) -- : A t α (next c κ α ρ)

-- Contexts as types.

ctx→ty : ∀ {ℓ} (c : Ctx ℓ)(d : Ctx ℓ)
  → (κ : Clock) → Ctx.Γ d κ → Set ℓ
ctx→ty (ctx Γ _ _) _ κ _ = Γ κ

ctx→ty-next : ∀ {ℓ} (c d : Ctx ℓ)
  → (κ : Clock) (α : Tick κ) (ρ : Ctx.Γ d κ)
  → ctx→ty c d κ ρ → ctx→ty c d α (Ctx.next d κ α ρ)
ctx→ty-next (ctx Γ n _) _ κ α _ = n κ α

ctx→ty-next-ass : ∀ {ℓ} (c d : Ctx ℓ)
  → (κ : Clock) (α : Tick κ) (β : Tick α) (ρ : Ctx.Γ d κ)
  → (x : ctx→ty c d κ ρ)
  → PathOver (ctx→ty c d β) (Ctx.next-ass d κ α β ρ)
             (ctx→ty-next c d α β (Ctx.next d κ α ρ) (ctx→ty-next c d κ α ρ x))
             (ctx→ty-next c d κ β ρ x)
ctx→ty-next-ass (ctx Γ n a) _ κ α β _ x = ↓-cst-in (a κ α β x)

Ctx→Ty : ∀ {ℓ} → Ctx ℓ → (d : Ctx ℓ) → Ty ℓ d
Ctx→Ty c d = ty (ctx→ty c d) (ctx→ty-next c d) (ctx→ty-next-ass c d)
