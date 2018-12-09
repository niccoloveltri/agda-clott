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

{-
□map : {n : ℕ} (Γ : Ctx n) (A B : Ty (suc n)) (i : Name (suc n))
  → Tm (WC Γ i) (A ⇒ B) → Tm Γ (□ A i ⇒ □ B i)
□map Γ A B i f = lambda Γ (□ A i) (□ B i)
                          (clock-abs i (Γ ,, □ A i) B
                                     (app {_} {WC (Γ ,, □ A i) i} {A} {B}
                                          (weaken (WC Γ i) (WC (□ A i) i) (A ⇒ B) f )
                                          (unsubst-tm (Γ ,, □ A i) A i {!!}
                                                      (clock-app {_} {Γ ,, □ A i} {A} i {!!} (var Γ (□ A i))))))
-}


module ty-iso₂ {n : ℕ} (Γ : Ctx n) (A B : Ty (suc n)) (i : Name (suc n)) where

  private X = (□ A i) ⊕ (□ B i)
  private Y = □ (A ⊕ B) i

  from-sum : Tm Γ (X ⇒ Y)
  from-sum = lambda Γ X Y (sum-rec  Γ (□ A i) (□ B i) Y
                                    (□map (Γ ,, □ A i) A (A ⊕ B) i
                                          (lambda (WC (Γ ,, □ A i) i) A (A ⊕ B)
                                                  (inl (WC (Γ ,, □ A i) i ,, A) A B
                                                        (var (WC (Γ ,, □ A i) i) A)))
                                          (var Γ (□ A i)))
                                    (□map (Γ ,, □ B i) B (A ⊕ B) i
                                          (lambda (WC (Γ ,, □ B i) i) B (A ⊕ B)
                                                  (inr (WC (Γ ,, □ B i) i ,, B) A B
                                                       (var (WC (Γ ,, □ B i) i) B)))
                                          (var Γ (□ B i))))

  to-sum : Tm Γ (Y ⇒ X)
  proj₁ (proj₁ to-sum Δ x) Δ' (y , p) = {!!}
  proj₂ (proj₁ to-sum Δ x) Δ' Δ'' (y , p) = {!!}
  proj₂ to-sum = {!!}

module ty-iso₃ {n : ℕ} (Γ : Ctx n) (A B : Ty (suc n)) (i : Name (suc n)) where

  private X = (□ A i) ⊗ (□ B i)
  private Y = □ (A ⊗ B) i

  from-prod : Tm Γ (X ⇒ Y)
  from-prod = lambda Γ X Y
                     (clock-abs i (Γ ,, X) (A ⊗ B)
                                (pair (WC (Γ ,, X) i) A B
                                      (clock-subst-ii (WC (Γ ,, X) i) A i
                                                      (clock-app (Γ ,, X) A i i
                                                                 (pr₁ (Γ ,, X) (□ A i) (□ B i)
                                                                      (var Γ X))))
                                      (clock-subst-ii (WC (Γ ,, X) i) B i
                                                      (clock-app (Γ ,, X) B i i
                                                                 (pr₂ (Γ ,, X) (□ A i) (□ B i)
                                                                      (var Γ X))))
                                 )
                     )

  to-prod : Tm Γ (Y ⇒ X)
  proj₁ (proj₁ (proj₁ (proj₁ to-prod Δ x) Δ' (y , p))) κ = proj₁ (y κ)
  proj₂ (proj₁ (proj₁ (proj₁ to-prod Δ x) Δ' (y , p))) κ α = cong proj₁ (p _ α)
  proj₁ (proj₂ (proj₁ (proj₁ to-prod Δ x) Δ' (y , p))) κ = proj₂ (y κ)
  proj₂ (proj₂ (proj₁ (proj₁ to-prod Δ x) Δ' (y , p))) κ α = cong proj₂ (p _ α)
  proj₂ (proj₁ to-prod Δ x) Δ' Δ'' (y , p) =
    path-prod
      (Σ≡-uip
        (funext (λ _ → funext (λ _ → uip)))
        refl)
      (Σ≡-uip
        (funext (λ _ → funext (λ _ → uip)))
        refl)
  proj₂ to-prod Δ Δ' x =
    Σ≡-uip
      (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
      refl

  to-from-prod : (x : Tm Γ X) → def-eq Γ X (app {_} {Γ} {Y} {X} to-prod (app {_} {Γ} {X} {Y} from-prod x)) x
  to-from-prod (x , p) Δ y =
    path-prod
      (Σ≡-uip
        (funext (λ _ → funext (λ _ → uip)))
        (funext (λ κ →
          begin
            Ty.Mor A _ _
                   (Ty.Mor A _ _
                           (Ty.Mor A _ _
                                   (proj₁ (proj₁ (x Δ y)) (insertClockCtx i κ Δ i))))
          ≡⟨ sym (Ty.MorComp A) ⟩
            Ty.Mor A _ _ 
                   (Ty.Mor A _ _
                           (proj₁ (proj₁ (x Δ y)) (insertClockCtx i κ Δ i)))
          ≡⟨ sym (Ty.MorComp A) ⟩
            Ty.Mor A _ _ (proj₁ (proj₁ (x Δ y)) (insertClockCtx i κ Δ i))
          ≡⟨ proj₂ (proj₁ (x Δ y)) (insertClockCtx i κ Δ i) _ ⟩
            proj₁ (proj₁ (x Δ y)) κ
          ∎
        )))
      (Σ≡-uip
        (funext (λ _ → funext (λ _ → uip)))
        (funext (λ κ →
          begin
            Ty.Mor B _ _
                   (Ty.Mor B _ _
                           (Ty.Mor B _ _
                                   (proj₁ (proj₂ (x Δ y)) (insertClockCtx i κ Δ i))))
          ≡⟨ sym (Ty.MorComp B) ⟩
            Ty.Mor B _ _ 
                   (Ty.Mor B _ _
                           (proj₁ (proj₂ (x Δ y)) (insertClockCtx i κ Δ i)))
          ≡⟨ sym (Ty.MorComp B) ⟩
            Ty.Mor B _ _ (proj₁ (proj₂ (x Δ y)) (insertClockCtx i κ Δ i))
          ≡⟨ proj₂ (proj₂ (x Δ y)) (insertClockCtx i κ Δ i) _ ⟩
            proj₁ (proj₂ (x Δ y)) κ
          ∎
        )))

  from-to-prod : (y : Tm Γ Y) → def-eq Γ Y (app {_} {Γ} {X} {Y} from-prod (app {_} {Γ} {Y} {X} to-prod y)) y
  from-to-prod (x , p) Δ y =
    Σ≡-uip
      (funext (λ _ → funext (λ _ → uip)))
      (funext (λ κ →
        path-prod
          (
            begin
              Ty.Mor A _ _
                     (Ty.Mor A _ _
                             (Ty.Mor A _ _
                                     (proj₁ (proj₁ (x Δ y) (insertClockCtx i κ Δ i)))))
            ≡⟨ sym (Ty.MorComp A) ⟩
              Ty.Mor A _ _
                     (Ty.Mor A _ _
                             (proj₁ (proj₁ (x Δ y) (insertClockCtx i κ Δ i))))
            ≡⟨ sym (Ty.MorComp A) ⟩
              Ty.Mor A _ _
                       (proj₁ (proj₁ (x Δ y) (insertClockCtx i κ Δ i)))
            ≡⟨ cong proj₁ (proj₂ (x Δ y) (insertClockCtx i κ Δ i) _) ⟩
              proj₁ (proj₁ (x Δ y) κ)
            ∎
          )
          (
            begin
              Ty.Mor B _ _
                     (Ty.Mor B _ _
                             (Ty.Mor B _ _
                                     (proj₂ (proj₁ (x Δ y) (insertClockCtx i κ Δ i)))))
            ≡⟨ sym (Ty.MorComp B) ⟩
              Ty.Mor B _ _
                     (Ty.Mor B _ _
                             (proj₂ (proj₁ (x Δ y) (insertClockCtx i κ Δ i))))
            ≡⟨ sym (Ty.MorComp B) ⟩
              Ty.Mor B _ _
                       (proj₂ (proj₁ (x Δ y) (insertClockCtx i κ Δ i)))
            ≡⟨ cong proj₂ (proj₂ (x Δ y) (insertClockCtx i κ Δ i) _) ⟩
              proj₂ (proj₁ (x Δ y) κ)
            ∎
          )
        ))
