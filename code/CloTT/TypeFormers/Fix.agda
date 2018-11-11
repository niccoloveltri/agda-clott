module CloTT.TypeFormers.Fix where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.FunctionType


{-# TERMINATING #-}
{-
fix₁ : {n : ℕ} (Γ : Ctx n) (A : Ty n) (i : Name n)
          → (f : Tm Γ (Later A i ⇒ A))
          → (Δ : ClockCtx n) → Ctx.Obj Γ Δ → Ctx.Obj A Δ
dfix₁ : {n : ℕ} (Γ : Ctx n) (A : Ty n) (i : Name n)
          → (f : Tm Γ (Later A i ⇒ A))
          → (Δ : ClockCtx n) → Ctx.Obj Γ Δ → LaterObj A i Δ
fix₁ Γ A i (f , p) Δ x = proj₁ (f Δ x) _ (dfix₁ Γ A i (f , p) Δ x) 
force (proj₁ (dfix₁ Γ A i (f , p) Δ x)) α = fix₁ Γ A i (f , p) _ (Ctx.Mor Γ Δ _ x)
proj₂ (dfix₁ Γ A i (f , p) Δ x) α α' =
  begin
    Ctx.Mor A (Δ [ i ↦ α ]) _ (fix₁ Γ A i (f , p) (Δ [ i ↦ α ]) (Ctx.Mor Γ Δ _ x))
  ≡⟨ proj₂ (f (Δ [ i ↦ α ]) (Ctx.Mor Γ Δ _ x)) _ _ (dfix₁ Γ A i (f , p) (Δ [ i ↦ α ]) (Ctx.Mor Γ Δ _ x)) ⟩
    proj₁ (f (Δ [ i ↦ α ]) (Ctx.Mor Γ Δ _ x)) _
          (LaterMor A i (Δ [ i ↦ α ]) _
                    (dfix₁ Γ A i (f , p) (Δ [ i ↦ α ]) (Ctx.Mor Γ Δ _ x)))
  ≡⟨ {!proj₂ (dfix₁ Γ A i (f , p) (Δ [ i ↦ α ]) (Ctx.Mor Γ Δ _ x)) α α' -- cong (proj₁ (f (Δ [ i ↦ α ]) (Ctx.Mor Γ Δ _ x)) _)!} ⟩
    fix₁ Γ A i (f , p) (Δ [ i ↦ α' ]) (Ctx.Mor Γ Δ _ x)
  ∎

fix : {n : ℕ} (Γ : Ctx n) (A : Ty n) (i : Name n)
          → (e : Tm Γ (Later A i ⇒ A)) → Tm Γ A
proj₁ (fix Γ A i e) = -- fix₁ Γ A i e          
proj₂ (fix Γ A i e) Δ Δ' x = {!!}
-}

dfix : {n : ℕ} (Γ : Ctx n) (A : Ty n) (i : Name n)
          → (e : Tm Γ (Later A i ⇒ A)) → Tm Γ (Later A i)
force (proj₁ (proj₁ (dfix Γ A i (f , p)) Δ x)) α = proj₁ (f Δ x) _ (proj₁ (dfix Γ A i (f , p)) (Δ [ i ↦ α ]) (Ctx.Mor Γ Δ _ x))
proj₂ (proj₁ (dfix Γ A i (f , p)) Δ x) α α' =
  begin
    Ctx.Mor A (Δ [ i ↦ α ]) _
            (proj₁ (f Δ x) _
              (proj₁ (dfix Γ A i (f , p)) (Δ [ i ↦ α ])
              (Ctx.Mor Γ Δ _ x)))
  ≡⟨ proj₂ (f Δ x) _ _ (proj₁ (dfix Γ A i (f , p)) (Δ [ i ↦ α ]) (Ctx.Mor Γ Δ _ x)) ⟩
    proj₁ (f Δ x) _
          (LaterMor A i (Δ [ i ↦ α ]) _
            (proj₁ (dfix Γ A i (f , p)) (Δ [ i ↦ α ])
            (Ctx.Mor Γ Δ _ x)))
  ≡⟨ cong (proj₁ (f Δ x) _) (proj₂ (dfix Γ A i (f , p)) (Δ [ i ↦ α ]) _ (Ctx.Mor Γ Δ _ x)) ⟩
    proj₁ (f Δ x) _ (proj₁ (dfix Γ A i (f , p)) (Δ [ i ↦ α' ])
                           (Ctx.Mor Γ (Δ [ i ↦ α ]) _
                           (Ctx.Mor Γ Δ _ x)))
  ≡⟨ cong (λ z → proj₁ (f Δ x) _ (proj₁ (dfix Γ A i (f , p)) (Δ [ i ↦ α' ]) z)) (sym (Ctx.MorComp Γ)) ⟩
    proj₁ (f Δ x) _ (proj₁ (dfix Γ A i (f , p)) (Δ [ i ↦ α' ])
                           (Ctx.Mor Γ Δ _ x))
  ∎
proj₂ (dfix Γ A i (f , p)) Δ Δ' x =
  Σ≡-uip
    (funext (λ { _ → funext (λ _ → uip) }))
    (bisim A i (funext λ {α → {!!}}))

fix : {n : ℕ} (Γ : Ctx n) (A : Ty n) (i : Name n)
          → (e : Tm Γ (Later A i ⇒ A)) → Tm Γ A
fix Γ A i e = app {_} {Γ} {Later A i} {A} e (dfix Γ A i e)
