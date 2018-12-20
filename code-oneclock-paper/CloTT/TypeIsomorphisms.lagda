\AgdaHide{
\begin{code}
module CloTT.TypeIsomorphisms where

open import Data.Product
open import Data.Sum
open import Prelude
open import CloTT.Structure
open import CloTT.TypeFormers
open import CloTT.TypeFormers.Force

open PSh
\end{code}
}

\begin{code}
□const-tm : (Γ : Ctx set) (A : Ty set) → Tm Γ (□ (WC A) ⇒ A)
□const-tm Γ A γ (x , _) = x ∞

module _ (Γ : Ctx set) (A : Ty tot) (B : Ty tot) where
  sum-lem₁ : (t : □ (A ⊕ B)) (x : Obj A ∞)
    → proj₁ t ∞ ≡ inj₁ x
    → Σ (□ A) (λ s → (i : Size) → proj₁ t i ≡ inj₁ (proj₁ s i))
  proj₁ (proj₁ (sum-lem₁ (t , p) x q)) i = Mor A ∞ i x
  proj₂ (proj₁ (sum-lem₁ (t , p) x q)) i j = sym (MorComp A)
  proj₂ (sum-lem₁ (t , p) x q) i =
    begin
      t i
    ≡⟨ sym (p ∞ i) ⟩
      Mor (A ⊕ B) ∞ i (t ∞)
    ≡⟨ cong (Mor (A ⊕ B) ∞ i) q ⟩
      inj₁ (Mor A ∞ i x)
    ∎

  sum-lem₂ : (t : □ (A ⊕ B)) (x : Obj B ∞)
    → proj₁ t ∞ ≡ inj₂ x
    → Σ (□ B) (λ s → (i : Size) → proj₁ t i ≡ inj₂ (proj₁ s i))
  proj₁ (proj₁ (sum-lem₂ (t , p) x q)) i = Mor B ∞ i x
  proj₂ (proj₁ (sum-lem₂ (t , p) x q)) i j = sym (MorComp B)
  proj₂ (sum-lem₂ (t , p) x q) i =
    begin
      t i
    ≡⟨ sym (p ∞ i) ⟩
      Mor (A ⊕ B) ∞ i (t ∞)
    ≡⟨ cong (Mor (A ⊕ B) ∞ i) q ⟩
      inj₂ (Mor B ∞ i x)
    ∎
  
  □sum-tm : Tm Γ (□ (A ⊕ B) ⇒ (□ A ⊕ □ B))
  □sum-tm γ (t , p) with t ∞ | inspect t ∞
  □sum-tm γ (t , p) | inj₁ x | [ eq ] = inj₁ (proj₁ (sum-lem₁ (t , p) x eq))
  □sum-tm γ (t , p) | inj₂ y | [ eq ] = inj₂ (proj₁ (sum-lem₂ (t , p) y eq))
\end{code}

-- Γ ⊢ □ (WC A) ≅ A

\begin{code}
module ty-iso₁ (Γ : Ctx set) (A : Ty set) where
  private X = A
  private Y = □ (WC A)

  f : Tm Γ (X ⇒ Y)
  f = lambda _ _ _ (box _ (WC A) (var (WC Γ) (WC A)))

  f-inv : Tm Γ (Y ⇒ X)
  f-inv γ (x , _) = x ∞

  f-is-iso₁ : (t : Tm Γ X) → def-eq Γ X (sem-app-map _ _ _ f-inv (sem-app-map _ _ _ f t)) t
  f-is-iso₁ t γ = refl

  f-is-iso₂ : (t : Tm Γ Y) → def-eq Γ Y (sem-app-map _ _ _ f (sem-app-map _ _ _ f-inv t)) t
  f-is-iso₂ t γ =
    Σ≡-uip
      (funext (λ { _ → funext (λ _ → uip) }))
      (funext (proj₂ (t γ) ∞))
\end{code}

-- Γ ⊢ □ (⊳ A) ≅ □ A

\begin{code}
module ty-iso₂ (Γ : Ctx set) (A : Ty tot) where
  private X = □ (▻ A)
  private Y = □ A

  f : Tm Γ (X ⇒ Y)
  f = lambda _ _ _ (force-tm _ A (var _ _))

  f-inv : Tm Γ (Y ⇒ X)
  f-inv = lambda Γ Y X
                 (box (Γ ,, Y) (▻ A)
                      (pure (WC (Γ ,, Y)) A
                            (unbox (Γ ,, Y) A
                                   (var Γ Y))))

  f-is-iso₁ : (t : Tm Γ X) → def-eq Γ X (sem-app-map _ _ _ f-inv (sem-app-map _ _ _ f t)) t
  f-is-iso₁ t γ =
    Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
           (funext (λ i → Σ≡-uip (funext (λ { [ _ ] → funext (λ { [ _ ] → uip}) }))
                                 (funext (λ { [ j ] → cong (λ a → proj₁ a [ j ]) (proj₂ (t γ) ∞ i) }))))

  f-is-iso₂ : (t : Tm Γ Y) → def-eq Γ Y (sem-app-map _ _ _ f (sem-app-map _ _ _ f-inv t)) t
  f-is-iso₂ t γ =
    Σ≡-uip
      (funext (λ _ → funext (λ _ → uip)))
      refl
\end{code}

-- Γ ⊢ □ (WC A ⇒ B) ≅ (A ⇒ □ B)

\begin{code}
module ty-iso₃ (Γ : Ctx set) (A : Ty set) (B : Ty tot) where
  X =  □ (WC A ⇒ B)
  Y = A ⇒ □ B

  f : Tm Γ (X ⇒ Y)
  f = lambda Γ X Y
             (lambda (Γ ,, X) A (□ B)
                     (□map ((Γ ,, X) ,, A) (WC A) B
                           (weaken (WC (Γ ,, X)) (WC A) (WC A ⇒ B)
                                   (unbox (Γ ,, X) (WC A ⇒ B)
                                          (var Γ X)))
                           (box ((Γ ,, X) ,, A) (WC A)
                                (var (WC (Γ ,, X)) (WC A)))))
  

  f-inv : Tm Γ (Y ⇒ X)
  f-inv = lambda Γ Y X
             (box (Γ ,, Y) (WC A ⇒ B)
                  (lambda (WC (Γ ,, Y)) (WC A) B
                          (unbox ((Γ ,, Y) ,, A) B
                                 (sem-app-map ((Γ ,, Y) ,, A) A (□ B)
                                      (weaken (Γ ,, Y) A (A ⇒ □ B)
                                              (var Γ Y))
                                      (var (Γ ,, Y) A)))))

  f-is-iso₁ : ∀ t → def-eq Γ X (sem-app-map _ _ _ f-inv (sem-app-map _ _ _ f t)) t
  f-is-iso₁ t γ =
    Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
           (funext (λ i → Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
                                 (funext (λ j → funext (λ x → cong (λ a → proj₁ a j x) (sym (proj₂ (t γ) i j)))))))

  f-is-iso₂ : ∀ t → def-eq Γ Y (sem-app-map _ _ _ f (sem-app-map _ _ _ f-inv t)) t
  f-is-iso₂ t γ = funext (λ _ → Σ≡-uip (funext (λ { _ → funext (λ _ → uip) })) refl)
\end{code}

-- Γ ⊢ □ (A × B) ≅ □ A × □ B

\begin{code}
module ty-iso₄ (Γ : Ctx set) (A B : Ty tot) where
  X =  □ (A ⊗ B)
  Y = □ A ⊗ □ B

  f : Tm Γ (X ⇒ Y)
  f = lambda Γ X Y
             (pair (Γ ,, X) (□ A) (□ B)
                   (□map (Γ ,, X) (A ⊗ B) A
                         (lambda (WC (Γ ,, X)) (A ⊗ B) A
                                 (pr₁ (WC (Γ ,, X) ,, (A ⊗ B)) A B
                                      (var (WC (Γ ,, X)) (A ⊗ B))))
                         (var Γ X))
                   (□map (Γ ,, X) (A ⊗ B) B
                         (lambda (WC (Γ ,, X)) (A ⊗ B) B
                                 (pr₂ (WC (Γ ,, X) ,, (A ⊗ B)) A B
                                      (var (WC (Γ ,, X)) (A ⊗ B))))
                         (var Γ X)))

  f-inv : Tm Γ (Y ⇒ X)
  f-inv = lambda Γ Y X
                 (box (Γ ,, Y) (A ⊗ B)
                      (pair (WC (Γ ,, Y)) A B
                            (unbox (Γ ,, Y) A
                                   (pr₁ (Γ ,, Y) (□ A) (□ B)
                                         (var Γ Y)))
                            (unbox (Γ ,, Y) B
                                   (pr₂ (Γ ,, Y) (□ A) (□ B)
                                         (var Γ Y)))))
                                         
  f-is-iso₁ : (t : Tm Γ X) → def-eq Γ X (sem-app-map _ _ _ f-inv (sem-app-map _ _ _ f t)) t
  f-is-iso₁ t γ = Σ≡-uip (funext (λ { _ → funext (λ _ → uip) })) refl

  f-is-iso₂ : (t : Tm Γ Y) → def-eq Γ Y (sem-app-map _ _ _ f (sem-app-map _ _ _ f-inv t)) t
  f-is-iso₂ t γ =
    cong₂ _,_ (Σ≡-uip (funext (λ { _ → funext (λ _ → uip) })) refl)
              (Σ≡-uip (funext (λ { _ → funext (λ _ → uip) })) refl)
\end{code}

\begin{code}
module ty-iso₅ (Γ : Ctx set) (A B : Ty tot) where
  X = □ A ⊕ □ B
  Y = □ (A ⊕ B)

  f : Tm Γ (X ⇒ Y)
  f = lambda Γ X Y
             (sum-rec Γ (□ A) (□ B) Y
                      (□map (Γ ,, □ A) A (A ⊕ B)
                            (lambda (WC (Γ ,, □ A)) A (A ⊕ B)
                                    (inl (WC (Γ ,, □ A) ,, A) A B
                                         (var (WC (Γ ,, □ A)) A)))
                            (var Γ (□ A)))
                      (□map (Γ ,, □ B) B (A ⊕ B)
                            (lambda (WC (Γ ,, □ B)) B (A ⊕ B)
                                    (inr (WC (Γ ,, □ B) ,, B) A B
                                         (var (WC (Γ ,, □ B)) B)))
                            (var Γ (□ B))))
  {-
  sum-lem₁ : (t : □ (A ⊕ B)) (x : Obj A ∞)
    → proj₁ t ∞ ≡ inj₁ x
    → Σ (□ A) (λ s → (i : Size) → proj₁ t i ≡ inj₁ (proj₁ s i))
  proj₁ (proj₁ (sum-lem₁ (t , p) x q)) i = Mor A ∞ i x
  proj₂ (proj₁ (sum-lem₁ (t , p) x q)) i j = sym (MorComp A)
  proj₂ (sum-lem₁ (t , p) x q) i =
    begin
      t i
    ≡⟨ sym (p ∞ i) ⟩
      Mor (A ⊕ B) ∞ i (t ∞)
    ≡⟨ cong (Mor (A ⊕ B) ∞ i) q ⟩
      inj₁ (Mor A ∞ i x)
    ∎

  sum-lem₂ : (t : □ (A ⊕ B)) (x : Obj B ∞)
    → proj₁ t ∞ ≡ inj₂ x
    → Σ (□ B) (λ s → (i : Size) → proj₁ t i ≡ inj₂ (proj₁ s i))
  proj₁ (proj₁ (sum-lem₂ (t , p) x q)) i = Mor B ∞ i x
  proj₂ (proj₁ (sum-lem₂ (t , p) x q)) i j = sym (MorComp B)
  proj₂ (sum-lem₂ (t , p) x q) i =
    begin
      t i
    ≡⟨ sym (p ∞ i) ⟩
      Mor (A ⊕ B) ∞ i (t ∞)
    ≡⟨ cong (Mor (A ⊕ B) ∞ i) q ⟩
      inj₂ (Mor B ∞ i x)
    ∎
  
  f-inv : Tm Γ (Y ⇒ X)
  f-inv γ (t , p) with t ∞ | inspect t ∞
  f-inv γ (t , p) | inj₁ x | [ eq ] = inj₁ (proj₁ (sum-lem₁ (t , p) x eq))
  f-inv γ (t , p) | inj₂ y | [ eq ] = inj₂ (proj₁ (sum-lem₂ (t , p) y eq))
  
  f-is-iso₁ : (t : Tm Γ Y) → def-eq Γ Y (sem-app-map _ _ _ f (sem-app-map _ _ _ f-inv t)) t
  f-is-iso₁ t γ with proj₁ (t γ) ∞ | inspect (proj₁ (t γ)) ∞
  f-is-iso₁ t γ | inj₁ x | [ eq ] =
    Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
           (funext (λ i → sym (proj₂ (sum-lem₁ (t γ) x eq) i)))
  f-is-iso₁ t γ | inj₂ y | [ eq ] = 
    Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
           (funext (λ i → sym (proj₂ (sum-lem₂ (t γ) y eq) i)))

  f-is-iso₂ : (t : Tm Γ X) → def-eq Γ X (sem-app-map _ _ _ f-inv (sem-app-map _ _ _ f t)) t
  f-is-iso₂ t γ with t γ
  f-is-iso₂ t γ | inj₁ (x , p) =
    cong inj₁ (Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
                      (funext (p ∞)))
  f-is-iso₂ t γ | inj₂ (y , p) = 
    cong inj₂ (Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
                      (funext (p ∞)))
  -}
\end{code}
