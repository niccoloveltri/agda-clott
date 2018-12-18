module CloTT.TypeIsomorphisms where

open import Data.Product
open import Data.Sum
open import Prelude
open import CloTT.Structure
open import CloTT.TypeFormers
open import CloTT.TypeFormers.Force

-- Γ ⊢ □ (WC A) ≅ A

module ty-iso₁ (Γ : Ctx set) (A : Ty set) where

  X = A
  Y = □ (WC A)

  f : Tm set Γ (X ⇒ Y)
  proj₁ (f γ x) _ = x
  proj₂ (f γ x) _ _ = refl

  f-inv : Tm set Γ (Y ⇒ X)
  f-inv γ (x , _) = x ∞

  f-is-iso₁ : ∀ t → def-eq Γ X (app f-inv (app f t)) t
  f-is-iso₁ t γ = refl

  f-is-iso₂ : ∀ t → def-eq Γ Y (app f (app f-inv t)) t
  f-is-iso₂ t γ =
    Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
           (funext (proj₂ (t γ) ∞))

-- Γ ⊢ □ (⊳ A) ≅ □ A

module ty-iso₂ (Γ : Ctx set) (A : Ty tot) where

  X = □ (▻ A)
  Y = □ A

  f : Tm set Γ (X ⇒ Y)
  proj₁ (f γ (t , p)) i = proj₁ (t ∞) [ i ]
  proj₂ (f γ (t , p)) i j = proj₂ (t ∞) [ i ] [ j ]

  f-inv : Tm set Γ (Y ⇒ X)
  proj₁ (proj₁ (f-inv γ (t , p)) i) [ j ] = t j
  proj₂ (proj₁ (f-inv γ (t , p)) i) [ j ] [ k ] = p j k
  proj₂ (f-inv γ t) i j =
    Σ≡-uip (funext (λ { [ _ ] → funext (λ { [ _ ] → uip}) }))
           (funext (λ { [ k ] → refl }))

  f-is-iso₁ : ∀ t → def-eq Γ X (app f-inv (app f t)) t
  f-is-iso₁ t γ =
    Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
           (funext (λ i → Σ≡-uip (funext (λ { [ _ ] → funext (λ { [ _ ] → uip}) }))
                                 (funext (λ { [ j ] → cong (λ a → proj₁ a [ j ]) (proj₂ (t γ) ∞ i) }))))

  f-is-iso₂ : ∀ t → def-eq Γ Y (app f (app f-inv t)) t
  f-is-iso₂ t γ = refl 

-- Γ ⊢ □ (WC A ⇒ B) ≅ (A ⇒ □ B)

module ty-iso₃ (Γ : Ctx set) (A : Ty set) (B : Ty tot) where

  X =  □ (WC A ⇒ B)
  Y = A ⇒ □ B

  f : Tm set Γ (X ⇒ Y)
  proj₁ (f γ (t , p) x) i = proj₁ (t i) i x
  proj₂ (f γ (t , p) x) i j =
    begin
      PSh.Mor B i j (proj₁ (t i) i x)
    ≡⟨ proj₂ (t i) i j x ⟩
      proj₁ (t i) j x
    ≡⟨ cong (λ a → proj₁ a j x) (p i j) ⟩
      proj₁ (t j) j x
    ∎

  f-inv : Tm set Γ (Y ⇒ X)
  proj₁ (proj₁ (f-inv γ t) i) j x = proj₁ (t x) j
  proj₂ (proj₁ (f-inv γ t) i) j k x = proj₂ (t x) j k
  proj₂ (f-inv γ t) i j = refl

  f-is-iso₁ : ∀ t → def-eq Γ X (app f-inv (app f t)) t
  f-is-iso₁ t γ =
    Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
           (funext (λ i → Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
                                 (funext (λ j → funext (λ x → cong (λ a → proj₁ a j x) (sym (proj₂ (t γ) i j)))))))

  f-is-iso₂ : ∀ t → def-eq Γ Y (app f (app f-inv t)) t
  f-is-iso₂ t γ = funext (λ _ → Σ≡-uip (funext (λ { _ → funext (λ _ → uip) })) refl)

-- Γ ⊢ □ (A × B) ≅ □ A × □ B

module ty-iso₄ (Γ : Ctx set) (A B : Ty tot) where

  X =  □ (A ⊗ B)
  Y = □ A ⊗ □ B

  f : Tm set Γ (X ⇒ Y)
  proj₁ (proj₁ (f γ (t , p))) i = proj₁ (t i)
  proj₂ (proj₁ (f γ (t , p))) i j = cong proj₁ (p i j)
  proj₁ (proj₂ (f γ (t , p))) i = proj₂ (t i)
  proj₂ (proj₂ (f γ (t , p))) i j = cong proj₂ (p i j)

  f-inv : Tm set Γ (Y ⇒ X)
  proj₁ (proj₁ (f-inv γ ((t₁ , _) , t₂)) i) = t₁ i
  proj₂ (proj₁ (f-inv γ (t₁ , (t₂ , _))) i) = t₂ i
  proj₂ (f-inv γ ((t₁ , p₁) , (t₂ , p₂))) i j = cong₂ _,_ (p₁ i j) (p₂ i j)
  
  f-is-iso₁ : ∀ t → def-eq Γ X (app f-inv (app f t)) t
  f-is-iso₁ t γ = Σ≡-uip (funext (λ { _ → funext (λ _ → uip) })) refl

  f-is-iso₂ : ∀ t → def-eq Γ Y (app f (app f-inv t)) t
  f-is-iso₂ t γ =
    cong₂ _,_ (Σ≡-uip (funext (λ { _ → funext (λ _ → uip) })) refl)
              (Σ≡-uip (funext (λ { _ → funext (λ _ → uip) })) refl)

module ty-iso₅ (Γ : Ctx set) (A B : Ty tot) where

  X = □ (A ⊕ B)
  Y = □ A ⊕ □ B

  sum-lem₁ : (t : □ (A ⊕ B)) (x : PSh.Obj A ∞)
    → proj₁ t ∞ ≡ inj₁ x
    → Σ (□ A) (λ s → (i : Size) → proj₁ t i ≡ inj₁ (proj₁ s i))
  proj₁ (proj₁ (sum-lem₁ (t , p) x q)) i = PSh.Mor A ∞ i x
  proj₂ (proj₁ (sum-lem₁ (t , p) x q)) i j = sym (PSh.MorComp A)
  proj₂ (sum-lem₁ (t , p) x q) i =
    begin
      t i
    ≡⟨ sym (p ∞ i) ⟩
      PSh.Mor (A ⊕ B) ∞ i (t ∞)
    ≡⟨ cong (PSh.Mor (A ⊕ B) ∞ i) q ⟩
      inj₁ (PSh.Mor A ∞ i x)
    ∎

  sum-lem₂ : (t : □ (A ⊕ B)) (x : PSh.Obj B ∞)
    → proj₁ t ∞ ≡ inj₂ x
    → Σ (□ B) (λ s → (i : Size) → proj₁ t i ≡ inj₂ (proj₁ s i))
  proj₁ (proj₁ (sum-lem₂ (t , p) x q)) i = PSh.Mor B ∞ i x
  proj₂ (proj₁ (sum-lem₂ (t , p) x q)) i j = sym (PSh.MorComp B)
  proj₂ (sum-lem₂ (t , p) x q) i =
    begin
      t i
    ≡⟨ sym (p ∞ i) ⟩
      PSh.Mor (A ⊕ B) ∞ i (t ∞)
    ≡⟨ cong (PSh.Mor (A ⊕ B) ∞ i) q ⟩
      inj₂ (PSh.Mor B ∞ i x)
    ∎

  f : Tm set Γ (X ⇒ Y)
  f γ (t , p) with t ∞ | inspect t ∞
  f γ (t , p) | inj₁ x | [ eq ] = inj₁ (proj₁ (sum-lem₁ (t , p) x eq))
  f γ (t , p) | inj₂ y | [ eq ] = inj₂ (proj₁ (sum-lem₂ (t , p) y eq))

  f-inv : Tm set Γ (Y ⇒ X)
  proj₁ (f-inv γ (inj₁ (t , p))) i = inj₁ (t i)
  proj₂ (f-inv γ (inj₁ (t , p))) i j = cong inj₁ (p i j)
  proj₁ (f-inv γ (inj₂ (t , p))) i = inj₂ (t i)
  proj₂ (f-inv γ (inj₂ (t , p))) i j = cong inj₂ (p i j)
  
  f-is-iso₁ : ∀ t → def-eq Γ X (app f-inv (app f t)) t
  f-is-iso₁ t γ with proj₁ (t γ) ∞ | inspect (proj₁ (t γ)) ∞
  f-is-iso₁ t γ | inj₁ x | [ eq ] =
    Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
           (funext (λ i → sym (proj₂ (sum-lem₁ (t γ) x eq) i)))
  f-is-iso₁ t γ | inj₂ y | [ eq ] = 
    Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
           (funext (λ i → sym (proj₂ (sum-lem₂ (t γ) y eq) i)))

  f-is-iso₂ : ∀ t → def-eq Γ Y (app f (app f-inv t)) t
  f-is-iso₂ t γ with t γ
  f-is-iso₂ t γ | inj₁ (x , p) =
    cong inj₁ (Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
                      (funext (p ∞)))
  f-is-iso₂ t γ | inj₂ (y , p) = 
    cong inj₂ (Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
                      (funext (p ∞)))



{-
-- □ (WC A) ≅ A

module ty-iso₁ (Γ : Ctx set) (A : Ty set) where

  X = A
  Y = □ (WC A)

  f : Tm set Γ A → Tm set Γ (□ (WC A))
  f t = box Γ (WC A) (WC-fun Γ A t)

  f-inv : Tm set Γ (□ (WC A)) → Tm set Γ A
  f-inv t = WC-unfun Γ A (unbox Γ (WC A) t) 

  f-is-iso₁ : ∀ t → def-eq Γ A (f-inv (f t)) t
  f-is-iso₁ t _ = refl

  f-is-iso₂ : ∀ t → def-eq Γ (□ (WC A)) (f (f-inv t)) t
  f-is-iso₂ t =
    trans-def-eq {!!} {!!}
-}
