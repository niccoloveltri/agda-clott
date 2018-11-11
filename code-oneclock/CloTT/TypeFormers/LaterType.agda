
module CloTT.TypeFormers.LaterType where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.FunctionType

-- pure

pure : (Γ : Ctx tot) (A : Ty tot) (t : Tm tot Γ A) → Tm tot Γ (▻ A)
proj₁ (proj₁ (pure Γ A (t , _)) i x) [ j ] = t j (PSh.Mor Γ i j x)
proj₂ (proj₁ (pure Γ A (t , p)) i x) j k = 
  begin
    PSh.Mor A j k (t j (PSh.Mor Γ i j x))
  ≡⟨ p j k (PSh.Mor Γ i j x)  ⟩
    t k (PSh.Mor Γ j k (PSh.Mor Γ i j x))
  ≡⟨ cong (t k) (sym (PSh.MorComp Γ)) ⟩
    t k (PSh.Mor Γ i k x)
  ∎
proj₂ (pure Γ A (t , p)) i j x =
  Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
         (funext (λ { [ k ] → cong (t k) (PSh.MorComp Γ) }))

-- fmap (also called _⊛_)

fmap : (Γ : Ctx tot) (A B : Ty tot) 
          → (f : Tm tot Γ (▻ (A ⇒ B))) (t : Tm tot Γ (▻ A))
          → Tm tot Γ (▻ B)
proj₁ (proj₁ (fmap Γ A B (f , _) (t , _)) i x) [ j ] = proj₁ (proj₁ (f i x) [ j ]) j (proj₁ (t i x) [ j ])
proj₂ (proj₁ (fmap Γ A B (f , p) (t , q)) i x) j k =
  begin
    PSh.Mor B j k (proj₁ (proj₁ (f i x) [ j ]) j (proj₁ (t i x) [ j ]))
  ≡⟨ proj₂ (proj₁ (f i x) [ j ]) j k (proj₁ (t i x) [ j ]) ⟩ 
    proj₁ (proj₁ (f i x) [ j ]) k (PSh.Mor A j k (proj₁ (t i x) [ j ]))
  ≡⟨ cong (proj₁ (proj₁ (f i x) [ j ]) k) (proj₂ (t i x) j k) ⟩
    proj₁ (proj₁ (f i x) [ j ]) k (proj₁ (t i x) [ k ]) 
  ≡⟨ cong (λ z → proj₁ z k (proj₁ (t i x) [ k ])) (sym (proj₂ (f i x) j j)) ⟩ 
    proj₁ (PSh.Mor (A ⇒ B) j j (proj₁ (f i x) [ j ])) k (proj₁ (t i x) [ k ])
  ≡⟨ cong (λ z → proj₁ z k (proj₁ (t i x) [ k ])) (proj₂ (f i x) j k) ⟩
    proj₁ (proj₁ (f i x) [ k ]) k (proj₁ (t i x) [ k ])
  ∎ 
proj₂ (fmap Γ A B (f , p) (e , q)) i j x =
  Σ≡-uip (funext (λ { _ → funext (λ _ → uip)}))
         (funext (λ { [ k ] → cong₂ (λ a b → proj₁ (proj₁ a [ k ]) k (proj₁ b [ k ])) (p i j x) (q i j x) }))

-- Computation rules

pure-fmap-pure : (Γ : Ctx tot) (A B : Ty tot) 
          → (f : Tm tot Γ (A ⇒ B)) (t : Tm tot Γ A)
          → def-eq Γ (▻ B) (fmap Γ A B (pure Γ (A ⇒ B) f) (pure Γ A t)) (pure Γ B (app {tot}{Γ}{A}{B} f t))
pure-fmap-pure Γ A B (f , p) (t , q) i x =
  Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
         (funext (λ { [ j ] → refl }))


pure-id-fmap : (Γ : Ctx tot) (A B : Ty tot) (t : Tm tot Γ (▻ A))
         → def-eq Γ (▻ A) (fmap Γ A A (pure Γ (A ⇒ A) (id-tm Γ A)) t) t
pure-id-fmap Γ A B (t , p) i γ = Σ≡-uip (funext (λ { _ → funext (λ _ → uip) })) (funext (λ { [ j ] → refl }))         

pure-comp-fmap : (Γ : Ctx tot) (A B C : Ty tot)
         → (g : Tm tot Γ (▻ (B ⇒ C))) (f : Tm tot Γ (▻ (A ⇒ B))) (t : Tm tot Γ (▻ A))
         → def-eq Γ
                  (▻ C)
                  (fmap Γ A C (fmap Γ (A ⇒ B) (A ⇒ C) (fmap Γ (B ⇒ C) ((A ⇒ B) ⇒ (A ⇒ C)) (pure Γ ((B ⇒ C) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))) (comp-tm Γ A B C)) g) f) t)
                  (fmap Γ B C g (fmap Γ A B f t))
pure-comp-fmap Γ A B C g f t i γ = Σ≡-uip (funext (λ { _ → funext (λ _ → uip) })) (funext (λ { [ j ] → refl}))

fmap-pure-fun : (Γ : Ctx tot) (A B : Ty tot) 
          → (f : Tm tot Γ (▻ (A ⇒ B))) (t : Tm tot Γ A)
          → def-eq Γ
                   (▻ B)
                   (fmap Γ A B f (pure Γ A t))
                   (fmap Γ (A ⇒ B) B (pure Γ ((A ⇒ B) ⇒ B) (lambda Γ (A ⇒ B) B (app {tot} {Γ ,, (A ⇒ B)} {A} {B} (var {tot} Γ (A ⇒ B)) (weaken {tot} Γ (A ⇒ B) A t)))) f)
fmap-pure-fun Γ A B (f , p) (t , q) i γ =
  Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
         (funext (λ { [ j ] → cong (λ a → proj₁ (proj₁ (f i γ) [ j ]) j (t j a)) (sym (PSh.MorId Γ))}))


{-
-- pure

pure : (Γ : Ctx tot) (A : Ty tot) (t : Tm tot Γ A) → Tm tot Γ (▻ A)
force (proj₁ (proj₁ (pure Γ A (t , _)) i x)) j = t j (PSh.Mor Γ i j x)
proj₂ (proj₁ (pure Γ A (t , p)) i x) j k =
  begin
    PSh.Mor A j k (t j (PSh.Mor Γ i j x))
  ≡⟨ p j k (PSh.Mor Γ i j x)  ⟩
    t k (PSh.Mor Γ j k (PSh.Mor Γ i j x))
  ≡⟨ cong (t k) (sym (PSh.MorComp Γ)) ⟩
    t k (PSh.Mor Γ i k x)
  ∎
proj₂ (pure Γ A (t , p)) i j x =
  Σ≡-uip (funext (λ { _ → funext (λ _ → uip)}))
         (bisim (funext (λ { k → cong (t k) (PSh.MorComp Γ) })))

-- fmap (also called _⊛_)

fmap : (Γ : Ctx tot) (A B : Ty tot) 
          → (f : Tm tot Γ (▻ (A ⇒ B))) (t : Tm tot Γ (▻ A))
          → Tm tot Γ (▻ B)
force (proj₁ (proj₁ (fmap Γ A B (f , _) (t , _)) i x)) j =
  proj₁ (force (proj₁ (f i x)) j) j (force (proj₁ (t i x)) j) 
proj₂ (proj₁ (fmap Γ A B (f , p) (t , q)) i x) j k =
  begin
    PSh.Mor B j k (proj₁ (force (proj₁ (f i x)) j) j (force (proj₁ (t i x)) j))
  ≡⟨ proj₂ (force (proj₁ (f i x)) j) j k (force (proj₁ (t i x)) j) ⟩
    proj₁ (force (proj₁ (f i x)) j) k (PSh.Mor A j k (force (proj₁ (t i x)) j))
  ≡⟨ cong (proj₁ (force (proj₁ (f i x)) j) k) (proj₂ (t i x) j k) ⟩
    proj₁ (force (proj₁ (f i x)) j) k (force (proj₁ (t i x)) k)
  ≡⟨ cong (λ z → proj₁ z k (force (proj₁ (t i x)) k)) (sym (proj₂ (f i x) j j)) ⟩
    proj₁ (PSh.Mor (A ⇒ B) j j (force (proj₁ (f i x)) j)) k (force (proj₁ (t i x)) k)
  ≡⟨ cong (λ z → proj₁ z _ (force (proj₁ (t i x)) _)) (proj₂ (f i x) j k) ⟩
    proj₁ (force (proj₁ (f i x)) k) k (force (proj₁ (t i x)) k)
  ∎ 
proj₂ (fmap Γ A B (f , p) (e , q)) i j x =
  Σ≡-uip (funext (λ { _ → funext (λ _ → uip)}))
         (bisim (funext (λ { k → cong₂ (λ a b → proj₁ (force (proj₁ a) k) k (force (proj₁ b) k)) (p i j x) (q i j x) })))

-}


{-


fmap₁₁ : {n : ℕ} (Γ : Ctx n) (A B : Ty n) (i : Name n)
          → (f : Tm Γ (Later (A ⇒ B) i)) (e : Tm Γ (Later A i))
          → (Δ : ClockCtx n) (x : Ctx.Obj Γ Δ)
          → ▻ B i Δ
force (fmap₁₁ Γ A B i (f , _) (e , _) Δ x) α = proj₁ (force (proj₁ (f Δ x)) α) _ (force (proj₁ (e Δ x)) α)

fmap₁₂ : {n : ℕ} (Γ : Ctx n) (A B : Ty n) (i : Name n)
         → (f : Tm Γ (Later (A ⇒ B) i)) (e : Tm Γ (Later A i))
         → (Δ : ClockCtx n) (x : Ctx.Obj Γ Δ)
         → (α : Size< (Δ i)) (α' : Size≤ α)
         → Ctx.Mor B (Δ [ i ↦ α ]) _
                   (proj₁ (force (proj₁ (proj₁ f Δ x)) α) _
                          (force (proj₁ (proj₁ e Δ x)) α))
           ≡
           proj₁ (force (proj₁ (proj₁ f Δ x)) (transSize<≤ {Δ i} {α} α')) _
                 (force (proj₁ (proj₁ e Δ x)) (transSize<≤ {Δ i} {α} α'))
fmap₁₂ Γ A B i (f , p) (e , q) Δ x α α' =
  begin
    Ctx.Mor B (Δ [ i ↦ α ]) _
                   (proj₁ (force (proj₁ (f Δ x)) α) _
                          (force (proj₁ (e Δ x)) α))
  ≡⟨ proj₂ (force (proj₁ (f Δ x)) α) _ _ (force (proj₁ (e Δ x)) α) ⟩
    proj₁ (force (proj₁ (f Δ x)) _) _ (Ctx.Mor A (Δ [ i ↦ α ]) _ (force (proj₁ (e Δ x)) _))
  ≡⟨ cong (proj₁ (force (proj₁ (f Δ x)) _) _) ((proj₂ (e Δ x)) α α') ⟩
    proj₁ (force (proj₁ (f Δ x)) α) _ (force (proj₁ (e Δ x)) _)
  ≡⟨ cong (λ z → proj₁ z _ (force (proj₁ (e Δ x)) _)) (sym (proj₂ (f Δ x) _ _)) ⟩ 
    proj₁ (Ctx.Mor (A ⇒ B) (Δ [ i ↦ α ]) _ (force (proj₁ (f Δ x)) α)) _(force (proj₁ (e Δ x)) _)
  ≡⟨ cong (λ z → proj₁ z _ (force (proj₁ (e Δ x)) _)) (proj₂ (f Δ x) α α') ⟩
    proj₁ (force (proj₁ (f Δ x)) (transSize<≤ {Δ i} {α} α')) _ (force (proj₁ (e Δ x)) _)
  ∎

fmap₂ : {n : ℕ} (Γ : Ctx n) (A B : Ty n) (i : Name n)
         → (f : Tm Γ (Later (A ⇒ B) i)) (e : Tm Γ (Later A i))
         → (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ) (x : Ctx.Obj Γ Δ)
         → (α : TickCtx Δ' i)
         → Ctx.Mor B (Δ [ i ↦ α ]) _
                   (proj₁ (force (proj₁ (proj₁ f Δ x)) (transSize≤< {Δ i} {Δ' i} α)) _
                          (force (proj₁ (proj₁ e Δ x)) (transSize≤< {Δ i} {Δ' i} α)))
           ≡
           proj₁ (force (proj₁ (proj₁ f Δ' (Ctx.Mor Γ Δ Δ' x))) α) _
                 (force (proj₁ (proj₁ e Δ' (Ctx.Mor Γ Δ Δ' x))) α)
fmap₂ Γ A B i (f , p) (e , q) Δ Δ' x α =
  begin
    Ctx.Mor B (Δ [ i ↦ α ]) _
              (proj₁ (force (proj₁ (f Δ x)) _) _
                     (force (proj₁ (e Δ x)) _))
  ≡⟨ proj₂ (force (proj₁ (f Δ x)) _) _ _ (force (proj₁ (e Δ x)) _) ⟩
    proj₁ (force (proj₁ (f Δ x)) _) _ (Ctx.Mor A (Δ [ i ↦ α ]) _ (force (proj₁ (e Δ x)) _))
  ≡⟨ cong (λ z → proj₁ (force (proj₁ z) _) _ (Ctx.Mor A (Δ [ i ↦ α ]) _ (force (proj₁ (e Δ x)) _))) (p Δ _ x) ⟩
    proj₁ (force (proj₁ (f Δ' (Ctx.Mor Γ Δ Δ' x))) α) _
          (Ctx.Mor A (Δ [ i ↦ α ]) _ (force (proj₁ (e Δ x)) _))
  ≡⟨ cong (λ z → proj₁ (force (proj₁ (f Δ' (Ctx.Mor Γ Δ Δ' x))) α) _ (force (proj₁ z) _)) (q Δ _ x) ⟩
    proj₁ (force (proj₁ (f Δ' (Ctx.Mor Γ Δ Δ' x))) α) _
          (force (proj₁ (e Δ' (Ctx.Mor Γ Δ Δ' x))) α)
  ∎

fmap : {n : ℕ} (Γ : Ctx n) (A B : Ty n) (i : Name n)
          → (f : Tm Γ (Later (A ⇒ B) i)) (e : Tm Γ (Later A i))
          → Tm Γ (Later B i)
proj₁ (proj₁ (fmap Γ A B i f e) Δ x) = fmap₁₁ Γ A B i f e Δ x
proj₂ (proj₁ (fmap Γ A B i f e) Δ x) α α' = fmap₁₂ Γ A B i f e Δ x α α'
proj₂ (fmap Γ A B i f e) Δ Δ' x =
  Σ≡-uip (funext (λ { _ → funext (λ _ → uip)}))
         (bisim B i (funext (λ {α → fmap₂ Γ A B i f e Δ Δ' x α})))

-}
