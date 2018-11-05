module CloTT.TypeFormers.Fix where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.FunctionType

insert-ii : {n : ℕ} (i : Name (suc n)) (j : Clock) (Δ : ClockCtx n) → insertClockCtx i j Δ i ≡ j
insert-ii i j Δ = {!!}

fix₁ : {n : ℕ} (Γ : Ctx (suc n)) (A : Ty (suc n)) (i : Name (suc n))
          → (f : Tm Γ (Later A i ⇒ A))
          → (Δ : ClockCtx n) → (j : Size)
          → Ctx.Obj Γ (insertClockCtx i j Δ) → Ctx.Obj A (insertClockCtx i j Δ)
dfix₁ : {n : ℕ} (Γ : Ctx (suc n)) (A : Ty (suc n)) (i : Name (suc n))
          → (f : Tm Γ (Later A i ⇒ A))
          → (Δ : ClockCtx n) → (j : Size)
          → Ctx.Obj Γ (insertClockCtx i j Δ) → LaterObj A i (insertClockCtx i j Δ)
fix₁ Γ A i (f , p) Δ j x = proj₁ (f (insertClockCtx i j Δ) x) _ (dfix₁ Γ A i (f , p) Δ j x)
force (proj₁ (dfix₁ Γ A i (f , p) Δ j x)) α = Ctx.Mor A (insertClockCtx i (subst (λ z → Size< z) (insert-ii i j Δ) α) Δ) _ (fix₁ Γ A i (f , p) Δ (subst (λ z → Size< z) (insert-ii i j Δ) α) (Ctx.Mor Γ (insertClockCtx i j Δ) _ x)) -- Ctx.Mor A (insertClockCtx i α Δ) _ (fix₁ Γ A i (f , p) Δ (subst (λ z → Size< z) (insert-ii i j Δ) α) (Ctx.Mor Γ (insertClockCtx i j Δ) (insertClockCtx i (subst (λ z → Size< z) (insert-ii i j Δ) α) Δ) x))
proj₂ (dfix₁ Γ A i (f , p) Δ j x) = {!!}

{-
fix₁ : {n : ℕ} (Γ : Ctx n) (A : Ty n) (i : Name n)
          → (f : Tm Γ (Later A i ⇒ A))
          → (Δ : ClockCtx n) → Ctx.Obj Γ Δ → Ctx.Obj A Δ
dfix₁ : {n : ℕ} (Γ : Ctx n) (A : Ty n) (i : Name n)
          → (f : Tm Γ (Later A i ⇒ A))
          → (Δ : ClockCtx n) → Ctx.Obj Γ Δ → LaterObj A i Δ
fix₁ Γ A i (f , p) Δ x = proj₁ (f Δ x) _ (dfix₁ Γ A i (f , p) Δ x) 
force (proj₁ (dfix₁ Γ A i (f , p) Δ x)) α = fix₁ Γ A i (f , p) {!!} (Ctx.Mor Γ Δ _ x)
proj₂ (dfix₁ Γ A i (f , p) Δ x) = {!!}
-}

fix : {n : ℕ} (Γ : Ctx n) (A : Ty n) (i : Name n)
          → (e : Tm Γ (Later A i ⇒ A)) → Tm Γ A
proj₁ (fix Γ A i e) = {!!}         
proj₂ (fix Γ A i e) = {!!}         

