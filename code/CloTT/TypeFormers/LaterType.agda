
module CloTT.TypeFormers.LaterType where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.FunctionType

-- pure

pure₁₁ : {n : ℕ} (Γ : Ctx n) (A : Ty n) (e : Tm Γ A) (i : Name n)
          → (Δ : ClockCtx n) (x : Ctx.Obj Γ Δ) → ▻ A i Δ
force (pure₁₁ Γ A (e , _) i Δ x) α = e (Δ [ i ↦ α ]) (Ctx.Mor Γ Δ _ x)

pure₁₂ : {n : ℕ} (Γ : Ctx n) (A : Ty n) (e : Tm Γ A) (i : Name n)
          → (Δ : ClockCtx n) (x : Ctx.Obj Γ Δ) (α : Tick (Δ i)) (α' : Size≤ α)
          → Ctx.Mor A (Δ [ i ↦ α ]) _ (proj₁ e (Δ [ i ↦ α ]) (Ctx.Mor Γ Δ _ x)) ≡
            proj₁ e (Δ [ i ↦ α' ]) (Ctx.Mor Γ Δ _ x)
pure₁₂ Γ A (e , p) i Δ x α α' = 
  begin
    Ctx.Mor A (Δ [ i ↦ α ]) _ (e (Δ [ i ↦ α ]) (Ctx.Mor Γ Δ _ x))
  ≡⟨ p (Δ [ i ↦ α ]) _ (Ctx.Mor Γ Δ _ x) ⟩
    e (Δ [ i ↦ α' ]) (Ctx.Mor Γ (Δ [ i ↦ α ]) _ (Ctx.Mor Γ Δ _ x))
  ≡⟨ cong (e (Δ [ i ↦ α' ])) (sym (Ctx.MorComp Γ)) ⟩
    e (Δ [ i ↦ α' ]) (Ctx.Mor Γ Δ _ x)
  ∎

pure₂ : {n : ℕ} (Γ : Ctx n) (A : Ty n) (e : Tm Γ A) (i : Name n)
          → (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ) (x : Ctx.Obj Γ Δ)
          → Bisim A i (LaterMor' A i Δ Δ' (pure₁₁ Γ A e i Δ x)) (pure₁₁ Γ A e i Δ' (Ctx.Mor Γ Δ Δ' x))
pure₂ Γ A (e , p) i Δ Δ' x = funext (λ {α → 
  begin
    Ctx.Mor A (Δ [ i ↦ α ]) _ (e (Δ [ i ↦ α ]) (Ctx.Mor Γ Δ _ x))
  ≡⟨ p (Δ [ i ↦ α ]) _ (Ctx.Mor Γ Δ _ x) ⟩
    e (Δ' [ i ↦ α ]) (Ctx.Mor Γ (Δ [ i ↦ α ]) _ (Ctx.Mor Γ Δ _ x))
  ≡⟨ cong (e (Δ' [ i ↦ α ])) (sym (Ctx.MorComp Γ)) ⟩
    e (Δ' [ i ↦ α ]) (Ctx.Mor Γ Δ _ x)
  ≡⟨ cong (e (Δ' [ i ↦ α ])) (Ctx.MorComp Γ) ⟩ 
    e (Δ' [ i ↦ α ]) (Ctx.Mor Γ Δ' _ (Ctx.Mor Γ Δ Δ' x))
  ∎})

pure : {n : ℕ} (Γ : Ctx n) (A : Ty n) (e : Tm Γ A) (i : Name n)
          → Tm Γ (Later A i)
proj₁ (proj₁ (pure Γ A e  i) Δ x) = pure₁₁ Γ A e i Δ x 
proj₂ (proj₁ (pure Γ A e  i) Δ x) = pure₁₂ Γ A e i Δ x
proj₂ (pure Γ A e i) Δ Δ' x = 
  Σ≡-uip (funext (λ { _ → funext (λ _ → uip)}))
         (bisim A i (pure₂ Γ A e i Δ Δ' x))

-- fmap (also called _⊛_)

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

pure-id : {n : ℕ} (Γ : Ctx n) (A : Ty n) (i : Name n) (u : Tm Γ (Later A i))
  → def-eq Γ (Later A i) (fmap Γ A A i (pure Γ (A ⇒ A) (id-tm Γ A) i) u) u 
pure-id Γ A i u Δ x =
  Σ≡-uip (funext (λ {_ → funext (λ _ → uip)}))
         (bisim A i refl)

pure-comp : {n : ℕ} (Γ : Ctx n) (A B C : Ty n) (i : Name n)
            (g : Tm Γ (Later (B ⇒ C) i)) (f : Tm Γ (Later (A ⇒ B) i)) (u : Tm Γ (Later A i))
  → def-eq Γ (Later C i)
           (fmap Γ A C i (fmap Γ (A ⇒ B) (A ⇒ C) i (fmap Γ (B ⇒ C) ((A ⇒ B) ⇒ (A ⇒ C)) i (pure Γ ((B ⇒ C) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))) (comp-tm Γ A B C) i) g) f) u)
           (fmap Γ B C i g (fmap Γ A B i f u))
pure-comp Γ A B C i g f u Δ x =
  Σ≡-uip (funext (λ {_ → funext (λ _ → uip)}))
         (bisim C i refl)

pure-app : {n : ℕ} (Γ : Ctx n) (A B : Ty n) (i : Name n) (t : Tm Γ (A ⇒ B)) (u : Tm Γ A)
  → def-eq Γ (Later B i) (fmap Γ A B i (pure Γ (A ⇒ B) t i) (pure Γ A u i)) (pure Γ B (app {_} {Γ} {A} {B} t u) i)
pure-app Γ A B i t u Δ x =
  Σ≡-uip (funext (λ {_ → funext (λ _ → uip)}))
         (bisim B i refl)

fmap-app : {n : ℕ} (Γ : Ctx n) (A B : Ty n) (i : Name n) (u : Tm Γ (Later (A ⇒ B) i)) (t : Tm Γ A)
  → def-eq Γ (Later B i)
           (fmap Γ A B i u (pure Γ A t i))
           (fmap Γ (A ⇒ B) B i (pure Γ ((A ⇒ B) ⇒ B) (lambda Γ (A ⇒ B) B (app {_} {Γ ,, (A ⇒ B)} {A} {B} (var Γ (A ⇒ B)) (weaken Γ (A ⇒ B) A t))) i) u)
fmap-app Γ A B i u t Δ x =
  Σ≡-uip (funext (λ {_ → funext (λ _ → uip)}))
         (bisim B i (funext λ {α →
           (cong (λ {z → proj₁ (force (proj₁ (proj₁ u Δ x)) α) _ (proj₁ t (Δ [ i ↦ α ]) z)}) (Ctx.MorComp Γ))}))
