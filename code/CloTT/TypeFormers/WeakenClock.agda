{-
Weakening of clock contexts.
From A : Ty n and a Name i we can make a type in Ty (S n).
We do this by leaving a position open, so we need i : Name (suc n).
-}
module CloTT.TypeFormers.WeakenClock where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure

module _ {n : ℕ} (A : Ty n) (i : Name (suc n)) where

  private module A = Ty A

  -- Object part
  WCObj : ClockCtx (suc n) → Set
  WCObj Δ = A.Obj (removeClock i Δ)

  -- Morphism part
  WCMor : (Δ : ClockCtx (suc n)) (Δ' : ClockCtx≤ Δ)
    → WCObj Δ → WCObj Δ'
  WCMor Δ Δ' x = A.Mor (removeClock i Δ) _ x

  -- Preservation of identity
  WCMorId : {Δ : ClockCtx (suc n)} {x : WCObj Δ}
    → WCMor Δ (coeClockCtx Δ) x ≡ x
  WCMorId = A.MorId

  -- Preservation of identity
  WCMorComp : {Δ : ClockCtx (suc n)} {Δ' : ClockCtx≤ Δ}
    {Δ'' : ClockCtx≤ Δ'} {x : WCObj Δ}
    → WCMor Δ _ x ≡ WCMor Δ' Δ'' (WCMor Δ Δ' x)
  WCMorComp = A.MorComp

  WC : Ty (suc n)
  WC = record
    { Obj = WCObj
    ; Mor = WCMor
    ; MorId = WCMorId
    ; MorComp = WCMorComp
    }

subst-tm : {n : ℕ} (Γ : Ctx (suc n)) (A : Ty (suc n)) (i : Name (suc n)) (j : Name (suc n)) (t : Tm Γ A)
  → Tm Γ (clock-subst A i j)
proj₁ (subst-tm Γ A i j (e , p)) Δ x =
  Ty.Mor A (insertClockCtx i (Δ j) (removeClock i Δ)) _
      (e (insertClockCtx i (Δ j) (removeClock i Δ))
       (Ctx.Mor Γ _ _ x))
proj₂ (subst-tm Γ A i j (e , p)) Δ Δ' x =
  begin
    Ty.Mor A _ _
           (Ty.Mor A _ _
                   (e (insertClockCtx i (Δ j) (removeClock i Δ))
                      (Ctx.Mor Γ Δ _ x)))
  ≡⟨ sym (Ty.MorComp A) ⟩
    Ty.Mor A _ _ (e (insertClockCtx i (Δ j) (removeClock i Δ))
                    (Ctx.Mor Γ Δ _ x))
  ≡⟨ p (insertClockCtx i (Δ j) (removeClock i Δ)) _ (Ctx.Mor Γ Δ _ x) ⟩
    e (Δ' [ i ↦ Δ' j ]) (Ctx.Mor Γ _ _ (Ctx.Mor Γ Δ _ x))
  ≡⟨ cong (e (Δ' [ i ↦ Δ' j ])) (sym (Ctx.MorComp Γ)) ⟩
    e (Δ' [ i ↦ Δ' j ]) (Ctx.Mor Γ Δ _ x)
  ≡⟨ cong (e (Δ' [ i ↦ Δ' j ])) (Ctx.MorComp Γ) ⟩
    e (Δ' [ i ↦ Δ' j ]) (Ctx.Mor Γ _ _ (Ctx.Mor Γ _ _ x))
  ≡⟨ sym (p (insertClockCtx i (Δ' j) (removeClock i Δ')) _ (Ctx.Mor Γ Δ _ x)) ⟩
    Ty.Mor A _ _ (e (insertClockCtx i (Δ' j) (removeClock i Δ'))
                    (Ctx.Mor Γ Δ _ x))
  ≡⟨ cong (λ z → Ty.Mor A _ _ (e (insertClockCtx i (Δ' j) (removeClock i Δ')) z)) (Ctx.MorComp Γ) ⟩
    Ty.Mor A _ _ (e (insertClockCtx i (Δ' j) (removeClock i Δ'))
                    (Ctx.Mor Γ Δ' _ (Ctx.Mor Γ Δ Δ' x)))
  ∎
{-
subst-tm : {n : ℕ} (Γ : Ctx n) (A : Ty (suc n)) (i : Name (suc n)) (j : Name n) (t : Tm (WC Γ i) A)
  → Tm Γ (clock-subst A i j)
proj₁ (subst-tm Γ A i j t) Δ x = proj₁ t (insertClockCtx i (Δ j) Δ) (Ctx.Mor Γ Δ _ x)
proj₂ (subst-tm Γ A i j t) Δ Δ' x =
  begin
    Ctx.Mor A (insertClockCtx i (Δ j) Δ) _
            (proj₁ t (insertClockCtx i (Δ j) Δ)
              (Ctx.Mor Γ Δ _ x))
  ≡⟨ proj₂ t (insertClockCtx i (Δ j) Δ) _ (Ctx.Mor Γ Δ _ x) ⟩
     proj₁ t (insertClockCtx i (Δ' j) Δ')
       (Ctx.Mor Γ (removeClock i (insertClockCtx i (Δ j) Δ)) _
         (Ctx.Mor Γ Δ _ x))
  ≡⟨ cong (proj₁ t (insertClockCtx i (Δ' j) Δ')) (sym (Ctx.MorComp Γ)) ⟩
    proj₁ t (insertClockCtx i (Δ' j) Δ') (Ctx.Mor Γ Δ _ x)
  ≡⟨ cong (proj₁ t (insertClockCtx i (Δ' j) Δ')) (Ctx.MorComp Γ) ⟩
    proj₁ t (insertClockCtx i (Δ' j) Δ') (Ctx.Mor Γ Δ' _ (Ctx.Mor Γ Δ Δ' x))
  ∎

unsubst-tm : {n : ℕ} (Γ : Ctx n) (A : Ty (suc n)) (i : Name (suc n)) (j : Name n) (t : Tm Γ (clock-subst A i j))
  → Tm (WC Γ i) A
proj₁ (unsubst-tm Γ A i j t) Δ x = Ty.Mor A (insertClockCtx i (removeClock i Δ j) _) _ (proj₁ t (removeClock i Δ) x)
proj₂ (unsubst-tm Γ A i j t) Δ Δ' x =
  begin
    Ty.Mor A Δ Δ'
      (Ty.Mor A (insertClockCtx i (removeClock i Δ j) (removeClock i Δ)) _
      (proj₁ t (removeClock i Δ) x))
  ≡⟨ sym (Ctx.MorComp A) ⟩
    Ty.Mor A (insertClockCtx i (removeClock i Δ j) (removeClock i Δ)) _
            (proj₁ t (removeClock i Δ) x)
  ≡⟨ Ty.MorComp A ⟩
    Ty.Mor A (insertClockCtx i (removeClock i Δ' j) (removeClock i Δ')) _
            (Ty.Mor A (insertClockCtx i (removeClock i Δ j) (removeClock i Δ)) _
              (proj₁ t (removeClock i Δ) x))
  ≡⟨ cong (Ty.Mor A (insertClockCtx i (removeClock i Δ' j) (removeClock i Δ')) _) (proj₂ t (removeClock i Δ) _ x) ⟩
    Ty.Mor A (insertClockCtx i (removeClock i Δ' j) (removeClock i Δ')) _
              (proj₁ t (removeClock i Δ') (Ctx.Mor Γ (removeClock i Δ) _ x))
  ∎
-}
