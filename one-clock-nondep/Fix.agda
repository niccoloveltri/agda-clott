module Fix where

open import LaterModality
open import Contexts
open import Pi
open import Types

-- Fixpoints.

fix : ∀{ℓ} (A : Clock → Set ℓ) (κ : Clock)
  → ((α : Tick= κ) → Later A α → A α)
  → A κ
dfix : ∀{ℓ} (A : Clock → Set ℓ) (κ : Clock)
  → ((α : Tick= κ) → Later A α → A α)
  → Later A κ
fix A κ g = g κ (dfix A κ g)
force (dfix A κ g) α = fix A α g

fix-eq : ∀{ℓ} (A : Clock → Set ℓ) (κ : Clock) 
  → (g : (α : Tick= κ) → Later A α → A α)
  → (α : Tick κ)
  → fix A α g ≡ g α (next⊳ A κ α (dfix A κ g))
dfix-eq : ∀{ℓ} (A : Clock → Set ℓ) (κ : Clock) 
  → (g : (α : Tick= κ) → Later A α → A α)
  → (α : Tick κ) {κ' : Clock}
  → dfix A α g ⊳[ κ' ]≡ next⊳ A κ α (dfix A κ g)
fix-eq A κ g α = cong (g α) (⊳≡ (dfix-eq A κ g α))
force-eq (dfix-eq A κ g α) β = funext λ {_ → refl}

fixᵀᵐ : ∀{ℓ} (c : ClTy ℓ) → ClTm ℓ ((⊳ c ⇒ c) ⇒ c)
fixᵀᵐ (ctx C nC aC) =
  tm (λ κ → pi (λ { α (pi g ng) → fix C α g })
               (λ {α β (pi g ng) →
                   begin
                 nC α β (g α (dfix C α g))
                   ≡⟨ ng α β (dfix C α g) ⟩
                 g β (next⊳ C α β (dfix C α g))
                   ≡⟨ cong (g β) (sym (⊳≡ (dfix-eq C α g β))) ⟩
                 g β (dfix C β g)
                   ∎}))
     (λ { _ _ → refl })


{-
-- Fixpoints.

fix : ∀{ℓ} (A : Clock → Set ℓ) (κ : Clock)
  → ((α : Tick= κ) → Later A (tick α) → A (tick α))
  → A κ
dfix : ∀{ℓ} (A : Clock → Set ℓ) (κ : Clock)
  → ((α : Tick= κ) → Later A (tick α) → A (tick α))
  → Later A κ
fix A κ g = g (κ , refl≤ˢ) (dfix A κ g)
force (dfix A κ g) α = fix A α (coe g α)

fix-eq : ∀{ℓ} (A : Clock → Set ℓ) (κ : Clock) 
  → (g : (α : Tick= κ) → Later A (tick α) → A (tick α))
  → (α : Tick κ)
  → fix A α (coe g α) ≡ g (α , <-≤ˢ α) (next⊳ A κ α (dfix A κ g))
dfix-eq : ∀{ℓ} (A : Clock → Set ℓ) (κ : Clock) 
  → (g : (α : Tick= κ) → Later A (tick α) → A (tick α))
  → (α : Tick κ) {κ' : Clock}
  → dfix A α (coe g α) ⊳[ κ' ]≡ next⊳ A κ α (dfix A κ g)
fix-eq A κ g α = cong (g (α , <-≤ˢ α)) (⊳≡ (dfix-eq A κ g α))
force-eq (dfix-eq A κ g α) β = funext dfix-eq'
  where
    dfix-eq' : (γ : Tick α)
      → fix A γ (coe (coe g α) γ) ≡ fix A γ (coe g γ)
    dfix-eq' γ = cong (fix A γ) (funext (coe-eq g α γ))


fix-τ : ∀{ℓ} (c : ClTy ℓ) (κ : Clock)
  → Ctx.Γ ((⊳ c ⇒ c) ⇒ c) κ
fix-τ c κ = pi fix-f fix-nextᶠ --fix-nextᶠ
  where
    open Ctx c
    fix-f : (α : Tick= κ) (g : Pi (⊳ c) (Ctx→Ty c (⊳ c)) (tick α)) → Γ (tick α)
    fix-f α (pi g _) = fix Γ (tick α) g

    fix-nextᶠ : (α : Tick= κ) (β : Tick (tick α))
      → (g : Pi (⊳ c) (Ctx→Ty c (⊳ c)) (tick α))
      → next (tick α) β (Pi.f g (tick α , refl≤ˢ) (dfix Γ (tick α) (Pi.f g)))
        ≡
        Pi.f g _ (dfix Γ β (nextᴾ-f (⊳ c) (Ctx→Ty c (⊳ c)) (tick α) β g))
    fix-nextᶠ α β (pi g p) =
      trans (p _ _ (dfix Γ (tick α) g)) (cong (g _) (sym (⊳≡ (dfix-eq Γ (tick α) g β))))

fix-nextᵀᵐ : ∀{ℓ} (c : ClTy ℓ) (κ : Clock) (α : Tick κ)
  → Ctx.next ((⊳ c ⇒ c) ⇒ c) κ α (fix-τ c κ) ≡ fix-τ c α
fix-nextᵀᵐ c κ α = Pi-eq refl
    
fixᵀᵐ : ∀{ℓ} (c : ClTy ℓ) → ClTm ℓ ((⊳ c ⇒ c) ⇒ c)
fixᵀᵐ c = tm (fix-τ c) (fix-nextᵀᵐ c)


-}
