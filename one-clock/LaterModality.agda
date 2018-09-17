module LaterModality where

open import Contexts
open import Pi

-- The later modality. The type ⊳ A κ looks like a dependent function
-- space, as in CloTT.

record Ltr {ℓ} (c : ClTy ℓ) (κ : Clock) : Set ℓ where 
  coinductive
  constructor ltr
  open Ctx c
  field force : (α : Tick κ) → Γ α
open Ltr public

-- We have to postulate extensional equality for the later modality. I
-- am not completely sure this is correct... Should this be defined
-- only on ⊳ A ∞ ? That's how it is done in the literature (Abel
-- papers) for other coinductive types.

record _⊳[_]≡_ {ℓ}
               {c : ClTy ℓ}
               {κ : Clock}
               (x : Ltr c κ)
               (κ' : Clock)
               (y : Ltr c κ) : Set ℓ where 
  coinductive
  constructor ltr-eq
  field force-eq : (α : Tick κ') → force x ≡ force y
open _⊳[_]≡_ public

postulate
  ⊳≡ : ∀ {ℓ} {c : ClTy ℓ} {κ : Clock} {x y : Ltr c κ} → x ⊳[ ∞ ]≡ y → x ≡ y


record Later {ℓ} (c : ClTy ℓ) (κ : Clock) : Set ℓ where
  constructor later
  open Ctx c
  field
    L : Ltr c κ
    nextᴸ : (α : Tick κ)(β : Tick α)
      → next α β (force L α) ≡ force L β

Later-eq : ∀ {ℓ} {c : ClTy ℓ} {κ : Clock} {x x' : Later c κ}
  → Later.L x ≡ Later.L x' → x ≡ x'
Later-eq {x = later L p}{later .L q} refl =
  cong (later L) (funext (λ {_ → funext (λ {_ → uip})}))


nextLtr : ∀{ℓ} (c : ClTy ℓ)
  → (κ : Clock) (α : Tick κ) → Ltr c κ → Ltr c α
force (nextLtr (ctx Γ nΓ _) κ α x) β = nΓ α β (force x α) --nΓ α β (force x α)

nextLater : ∀{ℓ} (c : ClTy ℓ)
  → (κ : Clock) (α : Tick κ) → Later c κ → Later c α
nextLater (ctx Γ nΓ aΓ) κ α (later x nx) =
  later (nextLtr (ctx Γ nΓ aΓ) κ α x)
        (λ {β γ → aΓ α β γ (force x α) })

nextLtr-ass : ∀{ℓ} (c : ClTy ℓ)
  → (κ : Clock) (α : Tick κ) (β : Tick α) {κ' : Clock} (x : Later c κ)
  → nextLtr c α β (nextLtr c κ α (Later.L x)) ⊳[ κ' ]≡ nextLtr c κ β (Later.L x)
force-eq (nextLtr-ass (ctx Γ nΓ aΓ) κ α β (later x nx)) _ =
  funext (λ {γ → trans (aΓ α β _ (force x α)) (trans (nx α _) (sym (nx β _)))})

nextLater-ass : ∀{ℓ} (c : ClTy ℓ) (κ : Clock) (α : Tick κ) (β : Tick α)
  → (x : Later c κ) → nextLater c α β (nextLater c κ α x) ≡ nextLater c κ β x
nextLater-ass c κ α β x = Later-eq (⊳≡ (nextLtr-ass c κ α β x ))

⊳ :  ∀{ℓ} → ClTy ℓ → ClTy ℓ
⊳ c = ctx (Later c) (nextLater c) (nextLater-ass c)


{-
next⊳-ass' : ∀{ℓ} (c : ClTy ℓ)
  → (κ : Clock) (α : Tick κ) (β : Tick α) {κ' : Clock} (x : Later c κ)
  → next⊳ c α β (next⊳ c κ α x) ⊳[ κ' ]≡ next⊳ c κ β x
force-eq (next⊳-ass' (ctx Γ nΓ aΓ) κ α β x) _ =
  funext (λ {γ → trans (aΓ α β _ (force x α)) {!!} }) --trans (aΓ α β _ (force x α)) {!force x α!} })

⊳ :  ∀{ℓ} → ClTy ℓ → ClTy ℓ
⊳ c = ctx (Later c) (next⊳ c) {!!}
-}

{-

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
  constructor later-eq
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
-}


