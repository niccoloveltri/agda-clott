module CloTT.TypeFormers.ClockQuantificationType where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.WeakenClock
open import CloTT.TypeFormers.ClockQuantification

clock-abs : {n : ℕ} (i : Name (suc n)) (Γ : Ctx n) (A : Ty (suc n)) (e : Tm (WC Γ i) A)
          → Tm Γ (□ A i)
proj₁ (proj₁ (clock-abs i Γ A (e , p)) Δ x) κ = e (insertClockCtx i κ Δ) (Ctx.Mor Γ Δ _ x)
proj₂ (proj₁ (clock-abs i Γ A (e , p)) Δ x) κ α =
  begin
    Ctx.Mor A (insertClockCtx i κ Δ) _
            (e (insertClockCtx i κ Δ)
               (Ctx.Mor Γ Δ _ x))
  ≡⟨ p (insertClockCtx i κ Δ) _ (Ctx.Mor Γ Δ _ x) ⟩
    e (insertClockCtx i α Δ)
      (Ctx.Mor Γ (removeClock i (insertClockCtx i κ Δ)) _
               (Ctx.Mor Γ Δ _ x))
  ≡⟨ cong (e (insertClockCtx i α Δ)) (sym (Ctx.MorComp Γ)) ⟩
    e (insertClockCtx i α Δ) (Ctx.Mor Γ Δ _ x)
  ∎
proj₂ (clock-abs i Γ A (e , p)) Δ Δ' x =
  Σ≡-uip (funext (λ _ → (funext λ _ → uip)))
         (funext (λ κ →
           begin
             Ctx.Mor A (insertClockCtx i κ Δ) _
                       (e (insertClockCtx i κ Δ)
                         (Ctx.Mor Γ Δ _ x))
           ≡⟨ p (insertClockCtx i κ Δ) _ (Ctx.Mor Γ Δ _ x) ⟩
             e (insertClockCtx i κ Δ')
               (Ctx.Mor Γ (removeClock i (insertClockCtx i κ Δ)) _
                        (Ctx.Mor Γ Δ _ x))
           ≡⟨ cong (e (insertClockCtx i κ Δ')) (sym (Ctx.MorComp Γ)) ⟩
             e (insertClockCtx i κ Δ') (Ctx.Mor Γ Δ _ x)
           ≡⟨ cong (e (insertClockCtx i κ Δ')) (Ctx.MorComp Γ) ⟩
             e (insertClockCtx i κ Δ')
               (Ctx.Mor Γ Δ' _
                 (Ctx.Mor Γ Δ Δ' x))
           ∎
         ))
{-  e (insertClockCtx i κ Δ) (subst (Ctx.Obj Γ) (remove-insert i κ) x)
proj₂ (proj₁ (clock-abs i Γ A (e , p)) Δ x) κ α =
  begin
    Ctx.Mor A (insertClockCtx i κ Δ) _ (e (insertClockCtx i κ Δ) (subst (Ctx.Obj Γ) (remove-insert i κ) x))
  ≡⟨ p (insertClockCtx i κ Δ) _ (subst (Ctx.Obj Γ) (remove-insert i κ) x) ⟩
    e (insertClockCtx i α Δ) (Ctx.Mor Γ (removeClock i (insertClockCtx i κ Δ)) _ (subst (Ctx.Obj Γ) (remove-insert i κ) x))
  ≡⟨ cong (e (insertClockCtx i α Δ))
       (begin
          Ctx.Mor Γ (removeClock i (insertClockCtx i κ Δ)) _           
            (subst (Ctx.Obj Γ) (remove-insert i κ) x)
        ≡⟨ cong₂-dep (λ y z → Ctx.Mor Γ y _ z)
                     (sym (remove-insert i κ))
                     (trans (subst-trans (remove-insert i κ) (sym (remove-insert i κ)))
                            (cong (λ y → subst (Ctx.Obj Γ) y x) uip)) ⟩
          Ctx.Mor Γ Δ _ x
        ≡⟨ sym (cong₂-dep (λ y z → Ctx.Mor Γ y _ z) (sym (remove-insert i α))
                     (trans (subst-trans (remove-insert i α) (sym (remove-insert i α))) (cong (λ y → subst (Ctx.Obj Γ) y x) uip))) ⟩
          Ctx.Mor Γ (removeClock i (insertClockCtx i α Δ)) _ (subst (Ctx.Obj Γ) (remove-insert i α) x)
        ∎) ⟩  
    e (insertClockCtx i α Δ) (Ctx.Mor Γ (removeClock i (insertClockCtx i α Δ)) _ (subst (Ctx.Obj Γ) (remove-insert i α) x))
  ≡⟨ cong (e (insertClockCtx i α Δ)) (Ctx.MorId Γ) ⟩  
    e (insertClockCtx i α Δ) (subst (Ctx.Obj Γ) (remove-insert i α) x)
  ∎
proj₂ (clock-abs i Γ A (e , p)) Δ Δ' x =
  Σ≡-uip (funext (λ _ → (funext λ _ → uip)))
         (funext (λ κ →
           begin
             Ctx.Mor A (insertClockCtx i κ Δ) _ (e (insertClockCtx i κ Δ) (subst (Ctx.Obj Γ) (remove-insert i κ) x))
           ≡⟨ p (insertClockCtx i κ Δ) _ (subst (Ctx.Obj Γ) (remove-insert i κ) x) ⟩  
             e (insertClockCtx i κ Δ') (Ctx.Mor Γ (removeClock i (insertClockCtx i κ Δ)) _ (subst (Ctx.Obj Γ) (remove-insert i κ) x))
           ≡⟨ cong (e (insertClockCtx i κ Δ'))
                (begin
                   Ctx.Mor Γ (removeClock i (insertClockCtx i κ Δ)) _ (subst (Ctx.Obj Γ) (remove-insert i κ) x)
                 ≡⟨ cong₂-dep (λ y z → Ctx.Mor Γ y _ z)
                              (sym (remove-insert i κ))
                              (trans (subst-trans (remove-insert i κ) (sym (remove-insert i κ)))
                                     (cong (λ y → subst (Ctx.Obj Γ) y x) uip)) ⟩
                   Ctx.Mor Γ Δ _ x
                 ≡⟨ sym (cong-dep (λ z → Ctx.Mor Γ Δ _ x) (remove-insert i κ)) ⟩
                   subst (Ctx.Obj Γ) (remove-insert i κ) (Ctx.Mor Γ Δ Δ' x)
                 ∎) ⟩   
             e (insertClockCtx i κ Δ') (subst (Ctx.Obj Γ) (remove-insert i κ) (Ctx.Mor Γ Δ Δ' x))
           ∎))
-}
clock-app : {n : ℕ} {Γ : Ctx n} {A : Ty (suc n)} (i : Name (suc n)) (j : Name n)
  → (e : Tm Γ (□ A i)) → Tm Γ (clock-subst A i j)
proj₁ (clock-app {n} {Γ} {A} i j (e , _)) Δ x = Ty.Mor A (insertClockCtx i (Δ j) Δ) _ (proj₁ (e Δ x) (Δ j))
proj₂ (clock-app {n} {Γ} {A} i j (e , p)) Δ Δ' x =
  begin
    Ctx.Mor A (insertClockCtx i (Δ j) Δ)
              _
              (Ctx.Mor A (insertClockCtx i (Δ j) Δ) _
                         (proj₁ (e Δ x) (Δ j)))
  ≡⟨ cong (Ctx.Mor A (insertClockCtx i (Δ j) Δ) _) (Ctx.MorId A) ⟩
    Ctx.Mor A (insertClockCtx i (Δ j) Δ) _ (proj₁ (e Δ x) (Δ j))
  ≡⟨ Ctx.MorComp A ⟩
    Ctx.Mor A (insertClockCtx i (Δ' j) Δ) _ (Ctx.Mor A (insertClockCtx i (Δ j) Δ) _ (proj₁ (e Δ x) (Δ j)))
  ≡⟨ cong (Ctx.Mor A (insertClockCtx i (Δ' j) Δ) _) (proj₂ (e Δ x) (Δ j) (Δ' j)) ⟩
    Ctx.Mor A (insertClockCtx i (Δ' j) Δ) _ (proj₁ (e Δ x) (Δ' j))
  ≡⟨ Ctx.MorComp A ⟩
    Ctx.Mor A (insertClockCtx i (Δ' j) Δ') _
              (Ctx.Mor A (insertClockCtx i (Δ' j) Δ) _
                         (proj₁ (e Δ x) (Δ' j)))
  ≡⟨ cong (λ z → Ctx.Mor A (insertClockCtx i (Δ' j) Δ') _ (proj₁ z (Δ' j))) (p Δ Δ' x) ⟩
    Ctx.Mor A (insertClockCtx i (Δ' j) Δ')
              _
              (proj₁ (e Δ' (Ctx.Mor Γ Δ Δ' x)) (Δ' j))
  ∎

clock-beta : {n : ℕ} (Γ : Ctx n) (A : Ty (suc n)) (i : Name (suc n)) (j : Name n) (t : Tm (WC Γ i) A)
  → def-eq Γ (clock-subst A i j)
           (clock-app {_} {Γ} {A} i j (clock-abs i Γ A t))
           (subst-tm Γ A i j t)
clock-beta Γ A i j t Δ x =
  begin
    Ctx.Mor A (insertClockCtx i (Δ j) Δ) _
            (proj₁ t (insertClockCtx i (Δ j) Δ)
                   (Ctx.Mor Γ Δ _ x))
  ≡⟨ Ty.MorId A ⟩
    proj₁ t (insertClockCtx i (Δ j) Δ) (Ctx.Mor Γ Δ _ x)
  ∎

clock-eta : {n : ℕ} (Γ : Ctx n) (A : Ty (suc n)) (i : Name (suc n)) (j : Name n) (e : Tm Γ (□ A i))
  → def-eq Γ (□ A i)
           (clock-abs i Γ A (unsubst-tm Γ A i j (clock-app {_} {Γ} {A} i j e)))
           e
clock-eta Γ A i j (e , p) Δ x =
  Σ≡-uip
    (funext (λ _ → funext (λ _ → uip)))
    (funext (λ κ →
      begin
        Ty.Mor A
          (insertClockCtx i (removeClock i (insertClockCtx i κ Δ) j) (removeClock i (insertClockCtx i κ Δ))) _
          (Ty.Mor A
            (insertClockCtx i (removeClock i (insertClockCtx i κ Δ) j) (removeClock i (insertClockCtx i κ Δ))) _
            (proj₁
              (e (removeClock i (insertClockCtx i κ Δ))
                 (Ctx.Mor Γ Δ _ x))
                 (removeClock i (insertClockCtx i κ Δ) j)))
      ≡⟨ sym (Ty.MorComp A) ⟩
        Ty.Mor A
          (insertClockCtx i (removeClock i (insertClockCtx i κ Δ) j) (removeClock i (insertClockCtx i κ Δ))) _
          (proj₁
            (e (removeClock i (insertClockCtx i κ Δ))
            (Ctx.Mor Γ Δ _ x))
              (removeClock i (insertClockCtx i κ Δ) j))
      ≡⟨ cong (λ z → Ty.Mor A (insertClockCtx i (removeClock i (insertClockCtx i κ Δ) j) (removeClock i (insertClockCtx i κ Δ))) _ (proj₁ z (removeClock i (insertClockCtx i κ Δ) j)))
              (sym (p Δ _ x)) ⟩
        Ty.Mor A
        (insertClockCtx i (removeClock i (insertClockCtx i κ Δ) j) (removeClock i (insertClockCtx i κ Δ))) _
        (Ty.Mor A
          (insertClockCtx i (removeClock i (insertClockCtx i κ Δ) j) Δ) _
          (proj₁ (e Δ x) (removeClock i (insertClockCtx i κ Δ) j)))
      ≡⟨ sym (Ty.MorComp A) ⟩
        Ty.Mor A
          (insertClockCtx i (removeClock i (insertClockCtx i κ Δ) j) Δ) _
          (proj₁ (e Δ x) (removeClock i (insertClockCtx i κ Δ) j))
      ≡⟨ proj₂ (e Δ x) (removeClock i (insertClockCtx i κ Δ) j) _ ⟩
        proj₁ (e Δ x) κ
      ∎
    ))
