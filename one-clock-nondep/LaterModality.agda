module LaterModality where

open import Types
open import Fun

-- The later modality. The type ⊳ A κ looks like a dependent function
-- space, as in CloTT.

record Ltr {ℓ} (t : Ty ℓ) (κ : Clock) : Set ℓ where 
  coinductive
  constructor ltr
  open Ty t
  field force : (α : Tick κ) → A α
open Ltr public

-- We postulate extensional equality for the later modality.

record _⊳[_]≡_ {ℓ}
               {t : Ty ℓ}
               {κ : Clock}
               (x : Ltr t κ)
               (κ' : Clock)
               (y : Ltr t κ) : Set ℓ where 
  coinductive
  constructor ltr-eq
  field force-eq : (α : Tick κ') → force x ≡ force y
open _⊳[_]≡_ public

postulate
  ⊳≡ : ∀ {ℓ} {t : Ty ℓ} {κ : Clock} {x y : Ltr t κ} → x ⊳[ ∞ ]≡ y → x ≡ y

record Later {ℓ} (t : Ty ℓ) (κ : Clock) : Set ℓ where
  constructor later
  open Ty t
  field
    L : Ltr t κ
    nextᴸ : (α : Tick κ)(β : Tick= α)
      → next α β (force L α) ≡ force L β

Later-eq : ∀ {ℓ} {t : Ty ℓ} {κ : Clock} {x x' : Later t κ}
  → Later.L x ≡ Later.L x' → x ≡ x'
Later-eq {x = later L p}{later .L q} refl =
  cong (later L) (funext (λ {_ → funext (λ {_ → uip})}))

⊳ :  ∀{ℓ} → Ty ℓ → Ty ℓ
⊳ t = ty (Later t) (λ _ _ → id) (λ _ _ _ _ → refl) (λ _ _ → refl) 

{-
nextLtr-ass : ∀{ℓ} (t : Ty ℓ)
  → (κ : Clock) (α : Tick κ) (β : Tick= α) {κ' : Clock} (x : Later t κ)
  → nextLtr t α β (nextLtr t κ α (Later.L x)) ⊳[ κ' ]≡ nextLtr t κ β (Later.L x)
force-eq (nextLtr-ass (ctx Γ nΓ aΓ) κ α β (later x nx)) _ =
-}

{-

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


-}
