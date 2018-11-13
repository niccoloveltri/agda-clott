module CloTT.TypeIsomorphisms where

open import Data.Product
open import Prelude
open import CloTT.Structure
open import CloTT.TypeFormers

module ty-iso₁ {n : ℕ} (Γ : Ctx n) (A : Ty n) (i : Name (suc n)) where

  private X = A
  private Y = □ (WC A i ) i

  to-wc : Tm Γ (X ⇒ Y)
  to-wc = lambda Γ X Y (clock-abs i (Γ ,, X) (WC A i) (var (WC Γ i) (WC A i)))

  from-wc : Tm Γ (Y ⇒ X)
  proj₁ (proj₁ from-wc Δ x) Δ' y = Ty.Mor A (removeClock i (insertClockCtx i ∞ Δ')) _ (proj₁ y ∞)
  proj₂ (proj₁ from-wc Δ x) Δ' Δ'' y =
    begin
      Ctx.Mor A Δ' _ (Ctx.Mor A (removeClock i (insertClockCtx i ∞ Δ')) _ (proj₁ y ∞))
    ≡⟨ sym (Ty.MorComp A) ⟩
      Ctx.Mor A (removeClock i (insertClockCtx i ∞ Δ')) _ (proj₁ y ∞)
    ≡⟨ Ty.MorComp A ⟩
      Ctx.Mor A (removeClock i (insertClockCtx i ∞ Δ'')) _ (proj₁ (Ctx.Mor Y Δ' _ y) ∞)
    ∎
  proj₂ from-wc Δ Δ' x = refl

  from-to-wc : (x : Tm Γ X) → def-eq Γ A (app {_} {Γ} {Y} {A} from-wc (app {_} {Γ} {A} {Y} to-wc x)) x
  from-to-wc (x , p) Δ y =
    begin
      Ty.Mor A (removeClock i (insertClockCtx i ∞ Δ)) _ (Ty.Mor A Δ _ (x Δ y))
    ≡⟨ sym (Ty.MorComp A) ⟩
      Ctx.Mor A Δ _ (x Δ y)
    ≡⟨ Ty.MorId A ⟩
      x Δ y
    ∎

  to-from-wc : (x : Tm Γ Y) → def-eq Γ Y (app {_} {Γ} {A} {Y} to-wc (app {_} {Γ} {Y} {A} from-wc x)) x
  to-from-wc (x , p) Δ y =
    Σ≡-uip
      (funext (λ _ → funext (λ _ → uip)))
      (funext (λ κ →
        begin
          Ty.Mor A Δ _ (Ty.Mor A (removeClock i (insertClockCtx i ∞ Δ)) _ (proj₁ (x Δ y) ∞))
        ≡⟨ sym (Ty.MorComp A) ⟩
          Ctx.Mor A (removeClock i (insertClockCtx i ∞ Δ)) _ (proj₁ (x Δ y) ∞)
        ≡⟨ proj₂ (x Δ y) ∞ κ ⟩
          proj₁ (x Δ y) κ
        ∎
      ))
