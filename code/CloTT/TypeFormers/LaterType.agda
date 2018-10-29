
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
  ≡⟨ cong (Ctx.Mor A (Δ [ i ↦ α ]) _) (sym (p Δ _ x)) ⟩
    Ctx.Mor A (Δ [ i ↦ α ]) _ (Ctx.Mor A Δ _ (e Δ x))
  ≡⟨ sym (Ctx.MorComp A) ⟩
    Ctx.Mor A Δ _ (e Δ x)
  ≡⟨ p Δ _ x ⟩
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
force (fmap₁₁ Γ A B i (f , _) (e , _) Δ x) α = {!app ? !}

fmap : {n : ℕ} (Γ : Ctx n) (A B : Ty n) (i : Name n)
          → (f : Tm Γ (Later (A ⇒ B) i)) (e : Tm Γ (Later A i))
          → Tm Γ (Later B i)
proj₁ (proj₁ (fmap Γ A B i f e) Δ x) = {!!}
proj₂ (proj₁ (fmap Γ A B i f e) Δ x) = {!!}
proj₂ (fmap Γ A B i f e) Δ Δ' x = {!!}
