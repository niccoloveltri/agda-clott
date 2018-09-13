module LaterModality where

open import Contexts

-- The later modality. The type ⊳ A κ looks like a dependent function
-- space, as in CloTT.

record Later {ℓ} (A : Clock → Set ℓ) (κ : Clock) : Set ℓ where 
  coinductive
  constructor later
  field force : (α : Tick κ) → A α
open Later public

-- We have to postulate extensional equality for the later modality. I
-- am not completely sure this is correct... Should this be defined
-- only on ⊳ A ∞ ? That's how it is done in the literature (Abel
-- papers) for other coinductive types.

record _⊳[_]≡_ {ℓ}
               {A : Clock → Set ℓ}
               {κ : Clock}
               (x : Later A κ)
               (κ' : Clock)
               (y : Later A κ) : Set ℓ where 
  coinductive
  field force-eq : (α : Tick κ') → force x ≡ force y
open _⊳[_]≡_ public

postulate
  ⊳≡ : ∀ {ℓ} {A : Clock → Set ℓ} {κ : Clock} {x y : Later A κ} → x ⊳[ ∞ ]≡ y → x ≡ y

next⊳ : ∀{ℓ} (A : Clock → Set ℓ)
  → (κ : Clock) (α : Tick κ) → Later A κ → Later A α
force (next⊳ A κ α x) = force x

next⊳-ass' : ∀{ℓ} (A : Clock → Set ℓ)
  → (κ : Clock) (α : Tick κ) (β : Tick α) {κ' : Clock} (x : Later A κ)
  → next⊳ A α β (next⊳ A κ α x) ⊳[ κ' ]≡ next⊳ A κ β x
force-eq (next⊳-ass' A κ α β x) γ = refl

next⊳-ass : ∀{ℓ} (A : Clock → Set ℓ) (κ : Clock) (α : Tick κ) (β : Tick α)
  → (x : Later A κ) → next⊳ A α β (next⊳ A κ α x) ≡ next⊳ A κ β x
next⊳-ass A κ α β x = ⊳≡ (next⊳-ass' A κ α β x)

⊳ :  ∀{ℓ} → ClTy ℓ → ClTy ℓ
⊳ (ctx A n a) = ctx (Later A) (next⊳ A) (next⊳-ass A)

