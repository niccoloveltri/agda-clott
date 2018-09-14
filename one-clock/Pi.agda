module Pi where

open import Types

uip : ∀{ℓ} {A : Set ℓ} → {a a' : A} → {p p' : a ≡ a'} → p ≡ p' 
uip {p = refl} {refl} = refl

uipOver : ∀{ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
  → {a a' : A} {p : a ≡ a'} {b : B a}{b' : B a'}
  → {q q' : b ≡ b' [ B ↓ p ]} → q ≡ q' 
uipOver {p = refl} = uip

postulate
  funext : ∀{ℓ ℓ'} {A : Set ℓ}{B : A → Set ℓ'}
    → {f g : (x : A) → B x}
    → ((x : A) → f x ≡ g x)
    → f ≡ g


-- Pi types.

record Pi {ℓ} (c : ClTy ℓ) (t : Ty ℓ c) (κ : Clock) : Set ℓ where
  constructor pi
  open Ctx c
  open Ty t
  field
    f : (α : Tick= κ) (x : Γ α) → A α x
    nextᶠ : (α : Tick= κ) (β : Tick α) (x : Γ α)
           → nextᵀʸ α β x (f α x) ≡ f β (next α β x) 

Fun : ∀{ℓ} → ClTy ℓ → ClTy ℓ → Clock → Set ℓ
Fun c d = Pi c (Ctx→Ty d c)

Pi-eq : ∀ {ℓ} {c : ClTy ℓ} {t : Ty ℓ c} {κ : Clock}
  → {g g' : Pi c t κ}
  → Pi.f g ≡ Pi.f g' → g ≡ g'
Pi-eq {κ = κ}{pi f p}{pi .f q} refl =
  cong (pi f) (funext (λ _ → funext (λ { _ → funext (λ _ → uip) })))

∏ : ∀ {ℓ} (c : ClTy ℓ) (t : Ty ℓ c) → ClTy ℓ
∏ c t = ctx (Pi c t) (λ { _ _ → id })  (λ { _ _ _ _ → refl })

_⇒_ : ∀ {ℓ} (c d : ClTy ℓ) → ClTy ℓ
c ⇒ d = ∏ c (Ctx→Ty d c)

app : ∀{ℓ} {c d : ClTy ℓ}
  → ClTm ℓ (c ⇒ d)
  → ClTm ℓ c → ClTm ℓ d
app {_}{ctx A nA aA} {ctx B nB aB} (tm g ng) (tm x nx) =
  tm (λ κ → Pi.f (g κ) κ (x κ))
     (λ {κ α →
        begin
       nB κ α (Pi.f (g κ) κ (x κ))
         ≡⟨ Pi.nextᶠ (g κ) κ α (x κ) ⟩
       Pi.f (g κ) α (nA κ α (x κ))
         ≡⟨ cong (Pi.f (g κ) α) (nx κ α) ⟩
       Pi.f (g κ) α (x α)
         ≡⟨ cong (λ z → Pi.f z α (x α)) (ng κ α) ⟩
       Pi.f (g α) α (x α)
         ∎})

I : ∀{ℓ} (c : ClTy ℓ) → ClTm ℓ (c ⇒ c)
I (ctx A nA aA) =
  tm (λ κ → pi (λ _ → id) (λ { _ _ _ → refl})) (λ { _ _ → refl })

_⊙_ : ∀{ℓ} {c d e : ClTy ℓ}
  → ClTm ℓ (d ⇒ e)
  → ClTm ℓ (c ⇒ d)
  → ClTm ℓ (c ⇒ e)
_⊙_ {_}{ctx C nC aC}{ctx D nD aD}{ctx E nE aE}(tm h nh) (tm g ng) =
  tm (λ κ → pi (λ α x → Pi.f (h κ) α (Pi.f (g κ) α x))
               (λ {α β x →
                    begin
                  nE α β (Pi.f (h κ) α (Pi.f (g κ) α x))
                    ≡⟨ Pi.nextᶠ (h κ) α β (Pi.f (g κ) α x) ⟩
                  Pi.f (h κ) β (nD α β (Pi.f (g κ) α x))
                    ≡⟨ cong (Pi.f (h κ) β) (Pi.nextᶠ (g κ) α β x) ⟩
                  Pi.f (h κ) β (Pi.f (g κ) β (nC α β x))
                    ∎}))
     (λ { κ α → Pi-eq (funext (λ β → funext (λ x →
         cong₂ (λ y z → Pi.f y β (Pi.f z β x)) (nh κ α) (ng κ α))))})


{-
-- Pi types.

record Pi {ℓ} (c : ClTy ℓ) (t : Ty ℓ c) (κ : Clock) : Set ℓ where
  constructor pi
  open Ctx c
  open Ty t
  field
    f : (α : Tick= κ) (x : Γ (tick α)) → A (tick α) x
    nextᶠ : (α : Tick= κ) (β : Tick (tick α)) (x : Γ (tick α))
           → nextᵀʸ (tick α) β x (f α x) ≡ f (coeˢ α β) (next (tick α) β x) 


Fun : ∀{ℓ} → ClTy ℓ → ClTy ℓ → Clock → Set ℓ
Fun c d = Pi c (Ctx→Ty d c)

--tick-input-eq : ∀{ℓ}{A : Set ℓ}
--  → {κ : Clock} {f g : Tick κ → A}
--  → ((α : Tick κ) → f α ≡ g α) → f ≡ g
--tick-input-eq p = funext p  

Pi-eq : ∀ {ℓ} {c : ClTy ℓ} {t : Ty ℓ c} {κ : Clock}
  → {g g' : Pi c t κ}
  → let open Pi g
        open Pi g' renaming (f to f')
  in f ≡ f' → g ≡ g'
Pi-eq {κ = κ}{pi f p}{pi .f q} refl = cong (pi f) (funext (λ α → funext (lem α)))
  where
    lem : (α : Tick= κ)(β : Tick (tick α)) → p α β ≡ q α β
    lem α β = funext (λ _ → uip)

nextᴾ-f : ∀ {ℓ} (c : ClTy ℓ) (t : Ty ℓ c) (κ : Clock)
  → (α : Tick κ) → Pi c t κ
  → let open Ctx c
        open Ty t
  in (β : Tick= α) (x : Γ (tick β)) → A (tick β) x
nextᴾ-f c t κ α g (β , p) x = f (β , trans≤ˢ p (<-≤ˢ α)) x
  where
    open Pi g

nextᴾ-nextᶠ : ∀ {ℓ} (c : ClTy ℓ) (t : Ty ℓ c) (κ : Clock)
  → (α : Tick κ) (g : Pi c t κ)
  → let open Ctx c
        open Ty t
  in (β : Tick= α) (γ : Tick (tick β)) (x : Γ (tick β)) →
      nextᵀʸ (tick β) γ x (nextᴾ-f c t κ α g β x) ≡
      nextᴾ-f c t κ α g (coeˢ β γ) (next (tick β) γ x)
nextᴾ-nextᶠ c t κ α g (.α , refl≤ˢ) γ x = nextᶠ (α , <-≤ˢ α) γ x
  where
    open Pi g
nextᴾ-nextᶠ c t κ α g (.β , <-≤ˢ β) γ x = nextᶠ (β , trans≤ˢ (<-≤ˢ β) (<-≤ˢ α)) γ x
  where
    open Pi g


nextᴾ : ∀ {ℓ} (c : ClTy ℓ) (t : Ty ℓ c) (κ : Clock)
  → (α : Tick κ) → Pi c t κ → Pi c t α
nextᴾ c t κ α g = pi (nextᴾ-f c t κ α g) (nextᴾ-nextᶠ c t κ α g)

nextᴾ-ass' : ∀ {ℓ} (c : ClTy ℓ) (t : Ty ℓ c) 
  → (κ : Clock) (α : Tick κ) (β : Tick α) (g : Pi c t κ) (γp : Tick= β)
  → let open Ctx c
        open Pi g
        γ , p = γp
  in (x : Γ γ)
  → f (γ , trans≤ˢ (trans≤ˢ p (<-≤ˢ β)) (<-≤ˢ α)) x
    ≡
    f (γ , trans≤ˢ p (<-≤ˢ β)) x
nextᴾ-ass' c t κ α β g (.β , refl≤ˢ) x = refl
nextᴾ-ass' c t κ α β g (.γ , <-≤ˢ γ) x = refl
  where
    open Pi g


nextᴾ-ass : ∀ {ℓ} (c : ClTy ℓ) (t : Ty ℓ c) 
  → (κ : Clock) (α : Tick κ) (β : Tick α) (g : Pi c t κ)
  → nextᴾ c t α β (nextᴾ c t κ α g) ≡ nextᴾ c t κ β g
nextᴾ-ass c t κ α β g = Pi-eq (funext (λ γ → funext (nextᴾ-ass' c t κ α β g γ)))

∏ : ∀ {ℓ} (c : ClTy ℓ) (t : Ty ℓ c) → ClTy ℓ
∏ c t = ctx (Pi c t) (nextᴾ c t) (nextᴾ-ass c t)

_⇒_ : ∀ {ℓ} (c d : ClTy ℓ) → ClTy ℓ
c ⇒ d = ∏ c (Ctx→Ty d c)



app : ∀{ℓ} {c d : ClTy ℓ}
  → ClTm ℓ (c ⇒ d)
  → ClTm ℓ c → ClTm ℓ d
app {_}{ctx A nA aA} {ctx B nB aB} (tm g' ng') (tm x nx) =
  tm (λ κ → g κ (κ , refl≤ˢ) (x κ)) r
  where
    g : (κ : Clock) (α : Tick= κ)
      → A (tick α) → B (tick α)
    g κ = Pi.f (g' κ)

    ng : (κ : Size) (α : Tick= κ) (β : Tick (tick α)) (y : A (tick α))
      → nB (tick α) β (g κ α y) ≡ g κ _ (nA (tick α) β y)
    ng κ = Pi.nextᶠ (g' κ)

    r : (κ : Clock) (α : Tick κ)
      → nB κ α (g κ (κ , refl≤ˢ) (x κ)) ≡ g α (α , refl≤ˢ) (x α)
    r κ α =
      trans (ng κ (κ , refl≤ˢ) α (x κ))
            (trans (cong (g κ (α , <-≤ˢ α)) (nx κ α))
                   (cong (λ z → Pi.f z (α , refl≤ˢ) (x α)) (ng' κ α)))


-- identity function

I-τ : ∀{ℓ} (c : ClTy ℓ) (κ : Clock) → Ctx.Γ (c ⇒ c) κ
I-τ c κ = pi (λ _ x → x) p
  where
    open Ctx c
    p : (α : Tick= κ) (β : Tick (tick α))
      → (x : Γ (tick α))
      → next (tick α) β x ≡ next (tick α) β x
    p _ _ _ = refl

I : ∀{ℓ} (c : ClTy ℓ) → ClTm ℓ (c ⇒ c)
I c = tm (I-τ c) p
  where
    open Ctx c
    p : (κ : Clock) (α : Tick κ) →
      Ctx.next (c ⇒ c) κ α (I-τ c κ) ≡ I-τ c α
    p κ α = Pi-eq refl


-- Composition of functions

Comp-τ : ∀{ℓ} {c d e : ClTy ℓ}
  → ClTm ℓ (d ⇒ e)
  → ClTm ℓ (c ⇒ d)
  → (κ : Clock) → Ctx.Γ (c ⇒ e) κ
Comp-τ {_}{ctx A nA _}{ctx B nB _}{ctx C nC _} (tm h' nh') (tm g' ng') κ =
  pi (λ α x → h κ α (g κ α x)) r
  where
    g : (κ : Clock) (α : Tick= κ)
      → A (tick α) → B (tick α)
    g κ = Pi.f (g' κ)

    ng : (κ : Size) (α : Tick= κ) (β : Tick (tick α)) (y : A (tick α))
      → nB (tick α) β (g κ α y) ≡ g κ _ (nA (tick α) β y)
    ng κ = Pi.nextᶠ (g' κ)

    h : (κ : Clock) (α : Tick= κ)
      → B (tick α) → C (tick α)
    h κ = Pi.f (h' κ)

    nh : (κ : Size) (α : Tick= κ) (β : Tick (tick α)) (y : B (tick α))
      → nC (tick α) β (h κ α y) ≡ h κ _ (nB (tick α) β y)
    nh κ = Pi.nextᶠ (h' κ)

    r : (α : Tick= κ) (β : Tick (tick α)) (x : A (tick α)) →
      nC (tick α) β (h κ α (g κ α x)) ≡ h κ (coeˢ α β) (g κ (coeˢ α β) (nA (tick α) β x))
    r α β x = trans (nh κ α β (g κ α x)) (cong (h κ (coeˢ α β)) (ng κ α β x))

Comp-nextᵀᵐ : ∀{ℓ} {c d e : ClTy ℓ}
  → (t : ClTm ℓ (d ⇒ e))
  → (s : ClTm ℓ (c ⇒ d))
  → (κ : Clock) (α : Tick κ)
  → Ctx.next (c ⇒ e) κ α (Comp-τ t s κ) ≡ Comp-τ t s α
Comp-nextᵀᵐ (tm h' nh') (tm g' ng') κ α =
  Pi-eq (funext (λ β → funext (λ x →
    trans (cong (λ z → Pi.f z β (Pi.f (g' κ) (proj₁ β , trans≤ˢ (proj₂ β) (<-≤ˢ α)) x)) (nh' κ α))
          (cong (Pi.f (h' α) β) (cong (λ z → Pi.f z β x) (ng' κ α))))))

_⊙_ : ∀{ℓ} {c d e : ClTy ℓ}
  → ClTm ℓ (d ⇒ e)
  → ClTm ℓ (c ⇒ d)
  → ClTm ℓ (c ⇒ e)
t ⊙ s = tm (Comp-τ t s) (Comp-nextᵀᵐ t s)


-}
