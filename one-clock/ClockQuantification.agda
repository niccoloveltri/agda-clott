module ClockQuantification where

open import Clocks
open import Contexts
open import Types
open import Pi
open import Id

-- Constant types

Const : ∀{ℓ} → Set ℓ → Clock → Set ℓ
Const A _ = A

next∁ : ∀{ℓ} → (A : Set ℓ)
  → (κ : Clock) (α : Tick κ) → Const A κ → Const A α
next∁ _ _ _ x = x

next∁-ass : ∀{ℓ} → (A : Set ℓ)
  → (κ : Clock) (α : Tick κ) (β : Tick α) (ρ : Const A κ)
  → next∁ A α β (next∁ A κ α ρ) ≡ next∁ A κ β ρ
next∁-ass _ _ _ _ _ = refl

∁ : ∀{ℓ} → Set ℓ → ClTy ℓ
∁ A = ctx (Const A) (next∁ A) (next∁-ass A)

record Box {ℓ} (c : ClTy ℓ) : Set ℓ where
  constructor box
  open Ctx c
  field
    lim : (κ : Clock) → Γ κ
    rest : (κ : Clock) (α : Tick κ) → next κ α (lim κ) ≡ lim α

Box-eq : ∀ {ℓ} {c : ClTy ℓ} {x x' : Box c}
  → let open Box x
        open Box x' renaming (lim to lim')
  in lim ≡ lim' → x ≡ x'
Box-eq {x = box l p}{box .l q} refl =
  cong (box l) (funext (λ κ → funext (r κ)))
  where
    r : (κ : Clock) (α : Tick κ) → p κ α ≡ q κ α
    r κ α = uip 

□ : ∀{ℓ} → ClTy ℓ → ClTy ℓ
□ c = ∁ (Box c)

□∁-f : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) (α : Tick= κ)
  → (x : Box (∁ A)) → A
□∁-f A κ α (box x p) = x κ₀

--□∁-nextᶠ : ∀{ℓ} (A : Set ℓ)
--  → (κ : Clock) (α : Tick= κ)

□∁-τ : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) → Fun (□ (∁ A)) (∁ A) κ
□∁-τ A κ = pi (□∁-f A κ) {!!}

□∁ : ∀{ℓ} (A : Set ℓ)
  → ClTm ℓ (□ (∁ A) ⇒ ∁ A)
□∁ A = tm (□∁-τ A) {!!}

□∁-inv-f : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) (α : Tick= κ)
  → (x : A) → Box (∁ A)
□∁-inv-f A κ α x = box (λ _ → x) r
  where
    r : ∀ κ' α' → _
    r _ _ = refl

□∁-inv-τ : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) → Fun (∁ A) (□ (∁ A)) κ
□∁-inv-τ A κ = pi (□∁-inv-f A κ) {!!}

□∁-inv : ∀{ℓ} (A : Set ℓ)
  → ClTm ℓ (∁ A ⇒ □ (∁ A))
□∁-inv A = tm (□∁-inv-τ A) {!!}


□∁-iso₁ : ∀{ℓ} (A : Set ℓ) (x : ClTm ℓ (∁ A))
  → ClTm ℓ (app (□∁ A) (app (□∁-inv A) x) ≡[ ∁ A ] x)
□∁-iso₁ A x = toId {x = app (□∁ A) (app (□∁-inv A) x)}{x} (λ _ → refl)

□∁-iso₂ : ∀{ℓ} (A : Set ℓ) (x : ClTm ℓ (□ (∁ A)))
  → ClTm ℓ (app (□∁-inv A) (app (□∁ A) x) ≡[ □ (∁ A) ] x)
□∁-iso₂ A (tm x nx) = toId {x = app (□∁-inv A) (app (□∁ A) (tm x nx))}{tm x nx}
  (λ κ → Box-eq (funext (λ κ' → Box.rest (x κ) κ₀ κ')))

{-

-- Clock quantification

Box : ∀{ℓ} → (Clock → Set ℓ) → Set ℓ
Box A = (κ : Clock) → A κ

□ : ∀{ℓ} → ClTy ℓ → ClTy ℓ
□ c = ∁ (Box Γ)
  where
    open Ctx c

□ᵀʸ : ∀{ℓ} (c : Ctx ℓ) → Ty ℓ c → Ty ℓ (□ c)
□ᵀʸ (ctx Γ nΓ aΓ) (ty A nA aA) =
  ty (λ _ ρ → (κ : Clock) → A κ (ρ κ)) q r
  where
    q : (i : Clock) (α : Tick i) (ρ : (κ : Clock) → Γ κ)
      → ((κ : Clock) → A κ (ρ κ)) → (κ : Clock) → A κ (ρ κ)
    q _ _ ρ x κ = x κ

    r : (i : Clock) (α : Tick i) (β : Tick α) (ρ : (κ : Clock) → Γ κ)
      → (x : (κ : Clock) → A κ (ρ κ)) → (λ κ → x κ) ≡ (λ κ → x κ)
    r _ _ _ _ _ = refl

-- Type isomorphisms

-- -- □ (∁ A) ≅ ∁ A

BoxConst-f : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) (α : Tick= κ) (x : Clock → A) → A
BoxConst-f A κ α x = x κ₀

BoxConst-nextᶠ : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) (α : Tick= κ) (β : Tick (tick α))
  → (x : Clock → A) → x κ₀ ≡ x κ₀
BoxConst-nextᶠ _ _ _ _ _ = refl

BoxConst : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) → Pi (□ (∁ A)) (Ctx→Ty (∁ A) (□ (∁ A))) κ
BoxConst A κ = pi (BoxConst-f A κ) (BoxConst-nextᶠ A κ) 

BoxConst-nextᵀᵐ : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) (α : Tick κ)
  → Ctx.next (□ (∁ A) ⇒ ∁ A) κ α (BoxConst A κ) ≡ BoxConst A α
BoxConst-nextᵀᵐ A κ α = Pi-eq (funext (λ _ → funext (λ x → refl)))

□∁ : ∀{ℓ} (A : Set ℓ)
  → ClTm ℓ (□ (∁ A) ⇒ ∁ A)
□∁ A = tm (BoxConst A) (BoxConst-nextᵀᵐ A)

BoxConst-inv-f : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) (α : Tick= κ) (x : A) (κ' : Clock) → A
BoxConst-inv-f A _ _ x _ = x

BoxConst-inv-nextᶠ : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) (α : Tick= κ) (β : Tick (tick α)) (x : A)
  → (λ (κ' : Clock) → x) ≡ (λ κ' → x)
BoxConst-inv-nextᶠ _ _ _ _ _ = refl  

BoxConst-inv : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) → Pi (∁ A) (Ctx→Ty (□ (∁ A)) (∁ A)) κ
BoxConst-inv A κ = pi (BoxConst-inv-f A κ) (BoxConst-inv-nextᶠ A κ)

BoxConst-inv-nextᵀᵐ : ∀{ℓ} (A : Set ℓ)
  → (κ : Clock) (α : Tick κ)
  → Ctx.next (∁ A ⇒ □ (∁ A)) κ α (BoxConst-inv A κ) ≡ BoxConst-inv A α
BoxConst-inv-nextᵀᵐ A κ α = Pi-eq refl

□∁-inv : ∀{ℓ} (A : Set ℓ)
  → ClTm ℓ (∁ A ⇒ □ (∁ A))
□∁-inv A = tm (BoxConst-inv A) (BoxConst-inv-nextᵀᵐ A)

□∁-iso₁ : ∀{ℓ} (A : Set ℓ) (x : ClTm ℓ (∁ A))
  → ClTm ℓ (app (□∁ A) (app (□∁-inv A) x) ≡[ ∁ A ] x)
□∁-iso₁ A x = toId {x = app (□∁ A) (app (□∁-inv A) x)} (λ _ → refl)

□∁-iso₂ : ∀{ℓ} (A : Set ℓ) (x : ClTm ℓ (□ (∁ A)))
  → ClTm ℓ (app (□∁-inv A) (app (□∁ A) x) ≡[ □ (∁ A) ] x)
□∁-iso₂ A (tm x nx) = toId {x = app (□∁-inv A) (app (□∁ A) (tm x nx))}
  {!!} --(λ κ → funext (λ κ' → {!nx κ₀ κ!}))

test : ∀{ℓ} (A : Set ℓ) (x : Box (Const A)) (κ : Clock)
  → x ∞ ≡ x κ
test A x = {!!}

-- □ (∏ (∁ A) B) ≅ ∏ (∁ A) (□ B)

□∏-f : ∀{ℓ} (X : Set ℓ) (t : Ty ℓ (∁ X))
  → (i : Clock) (α : Tick= i) (g : Ctx.Γ (□ (∏ (∁ X) t)) (tick α))
  → Ty.A (Ctx→Ty (∏ (□ (∁ X)) (□ᵀʸ (∁ X) t)) (□ (∏ (∁ X) t))) (tick α) g
□∏-f X (ty A nA aA) _ _ g' = pi (λ _ x κ → g κ (κ , refl≤ˢ) (x κ)) r
  where
    g : (κ : Clock) (α : Tick= κ) (x : X) → A (tick α) x
    g κ = Pi.f (g' κ)

    r : ∀ α β x → _
    r _ _ _ = refl

□∏-nextᶠ : ∀{ℓ} (X : Set ℓ) (t : Ty ℓ (∁ X))
  → (i : Clock) (α : Tick= i) (β : Tick (tick α))
  → (x : Ctx.Γ (□ (∏ (∁ X) t)) (tick α))
  → Ty.nextᵀʸ (Ctx→Ty (∏ (□ (∁ X)) (□ᵀʸ (∁ X) t)) (□ (∏ (∁ X) t))) (tick α) β x (□∏-f X t i α x)
    ≡
    □∏-f X t i (coeˢ α β) (Ctx.next (□ (∏ (∁ X) t)) (tick α) β x)
□∏-nextᶠ X t _ _ _ _ = Pi-eq refl
  
□∏-τ : ∀{ℓ} (X : Set ℓ) (t : Ty ℓ (∁ X))
  → (κ : Clock)
  → Ctx.Γ (□ (∏ (∁ X) t) ⇒ ∏ (□ (∁ X)) (□ᵀʸ (∁ X) t)) κ
□∏-τ X t _ = pi (□∏-f X t _) (□∏-nextᶠ X t _)

□∏-nextᵀᵐ : ∀{ℓ} (X : Set ℓ) (t : Ty ℓ (∁ X))
  → (κ : Clock)(α : Tick κ)
  → Ctx.next (□ (∏ (∁ X) t) ⇒ ∏ (□ (∁ X)) (□ᵀʸ (∁ X) t)) κ α (□∏-τ X t κ)
    ≡
    □∏-τ X t α
□∏-nextᵀᵐ X t _ _ = Pi-eq refl

□∏ : ∀{ℓ} (X : Set ℓ) (t : Ty ℓ (∁ X))
  → ClTm ℓ (□ (∏ (∁ X) t) ⇒ ∏ (□ (∁ X)) (□ᵀʸ (∁ X) t))
□∏ X t = tm (□∏-τ X t) (□∏-nextᵀᵐ X t)

□∏-inv-f : ∀{ℓ} (X : Set ℓ) (t : Ty ℓ (∁ X))
  → (κ : Clock) (α : Tick= κ)
  → (g : Ctx.Γ (∏ (□ (∁ X)) (□ᵀʸ (∁ X) t)) (tick α))
  → Ty.A (Ctx→Ty (□ (∏ (∁ X) t)) (∏ (□ (∁ X)) (□ᵀʸ (∁ X) t))) (tick α) g
□∏-inv-f X (ty A nA aA) _ β (pi g ng) κ =
  pi (λ α x → g ((tick β) , refl≤ˢ) (λ _ → x) (tick α)  ) r
  where
    r : ∀ α γ x → _
    r α γ x = {!ng!}


□∏-inv-τ : ∀{ℓ} (X : Set ℓ) (t : Ty ℓ (∁ X))
  → (κ : Clock)
  → Ctx.Γ (∏ (□ (∁ X)) (□ᵀʸ (∁ X) t) ⇒ □ (∏ (∁ X) t)) κ
□∏-inv-τ X t κ = pi (□∏-inv-f X t κ) {!!}

□∏-inv : ∀{ℓ} (X : Set ℓ) (t : Ty ℓ (∁ X))
  → ClTm ℓ (∏ (□ (∁ X)) (□ᵀʸ (∁ X) t) ⇒ □ (∏ (∁ X) t))
□∏-inv X t = tm {!!} {!!}
-}
