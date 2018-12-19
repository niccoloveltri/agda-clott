\AgdaHide{
\begin{code}
module CloTT.TypeFormers.LaterType where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.FunctionType

open PSh
\end{code}
}

\begin{code}
pure : (Γ : Ctx tot) (A : Ty tot) (t : Tm Γ A) → Tm Γ (▻ A)
proj₁ (proj₁ (pure Γ A (t , _)) i x) [ j ] = t j (Mor Γ i j x)
proj₂ (proj₁ (pure Γ A (t , p)) i x) [ j ] [ k ] = 
  begin
    Mor A j k (t j (Mor Γ i j x))
  ≡⟨ p j k (Mor Γ i j x)  ⟩
    t k (Mor Γ j k (Mor Γ i j x))
  ≡⟨ cong (t k) (sym (MorComp Γ)) ⟩
    t k (Mor Γ i k x)
  ∎
proj₂ (pure Γ A (t , p)) i j x =
  Σ≡-uip
    (funext (λ { [ _ ] → funext (λ { [ _ ] → uip }) }))
    (funext (λ { [ k ] → cong (t k) (MorComp Γ) }))
\end{code}

\begin{code}
fmap : (Γ : Ctx tot) (A B : Ty tot) 
          → (f : Tm Γ (▻ (A ⇒ B))) (t : Tm Γ (▻ A))
          → Tm Γ (▻ B)
proj₁ (proj₁ (fmap Γ A B (f , _) (t , _)) i x) [ j ] = proj₁ (proj₁ (f i x) [ j ]) j (proj₁ (t i x) [ j ])
proj₂ (proj₁ (fmap Γ A B (f , p) (t , q)) i x) [ j ] [ k ] =
  begin
    Mor B j k (proj₁ (proj₁ (f i x) [ j ]) j (proj₁ (t i x) [ j ]))
  ≡⟨ proj₂ (proj₁ (f i x) [ j ]) j k (proj₁ (t i x) [ j ]) ⟩ 
    proj₁ (proj₁ (f i x) [ j ]) k (Mor A j k (proj₁ (t i x) [ j ]))
  ≡⟨ cong (proj₁ (proj₁ (f i x) [ j ]) k) (proj₂ (t i x) [ j ] [ k ]) ⟩
    proj₁ (proj₁ (f i x) [ j ]) k (proj₁ (t i x) [ k ]) 
  ≡⟨ cong (λ z → proj₁ z k (proj₁ (t i x) [ k ])) (sym (proj₂ (f i x) [ j ] [ j ])) ⟩ 
    proj₁ (Mor (A ⇒ B) j j (proj₁ (f i x) [ j ])) k (proj₁ (t i x) [ k ])
  ≡⟨ cong (λ z → proj₁ z k (proj₁ (t i x) [ k ])) (proj₂ (f i x) [ j ] [ k ]) ⟩
    proj₁ (proj₁ (f i x) [ k ]) k (proj₁ (t i x) [ k ])
  ∎ 
proj₂ (fmap Γ A B (f , p) (e , q)) i j x =
  Σ≡-uip
    (funext (λ { [ _ ] → funext (λ { [ _ ] → uip })}))
    (funext (λ { [ k ] → cong₂ (λ a b → proj₁ (proj₁ a [ k ]) k (proj₁ b [ k ])) (p i j x) (q i j x) }))
\end{code}

\begin{code}
pure-fmap-pure : (Γ : Ctx tot) (A B : Ty tot) 
          → (f : Tm Γ (A ⇒ B)) (t : Tm Γ A)
          → def-eq Γ (▻ B)
                   (fmap Γ A B (pure Γ (A ⇒ B) f) (pure Γ A t))
                   (pure Γ B (sem-app-map Γ A B f t))
pure-fmap-pure Γ A B (f , p) (t , q) i x =
  Σ≡-uip
    (funext (λ { [ _ ] → funext (λ { [ _ ] → uip })}))
    (funext (λ { [ j ] → refl }))
\end{code}

\begin{code}
pure-id-fmap : (Γ : Ctx tot) (A B : Ty tot) (t : Tm Γ (▻ A))
         → def-eq Γ (▻ A)
                  (fmap Γ A A (pure Γ (A ⇒ A) (id-tm Γ A)) t)
                  t
pure-id-fmap Γ A B (t , p) i γ =
  Σ≡-uip
    (funext (λ { [ _ ] → funext (λ { [ _ ] → uip })}))
    (funext (λ { [ j ] → refl }))         
\end{code}

\begin{code}
pure-comp-fmap : (Γ : Ctx tot) (A B C : Ty tot)
         → (g : Tm Γ (▻ (B ⇒ C))) (f : Tm Γ (▻ (A ⇒ B))) (t : Tm Γ (▻ A))
         → def-eq Γ
                  (▻ C)
                  (fmap Γ A C
                        (fmap Γ (A ⇒ B) (A ⇒ C)
                              (fmap Γ (B ⇒ C) ((A ⇒ B) ⇒ (A ⇒ C))
                                    (pure Γ ((B ⇒ C) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))) (comp-tm Γ A B C))
                                    g)
                              f)
                        t)
                  (fmap Γ B C g (fmap Γ A B f t))
pure-comp-fmap Γ A B C g f t i γ =
  Σ≡-uip (funext (λ { [ _ ] → funext (λ { [ _ ] → uip })}))
         (funext (λ { [ j ] → refl}))
\end{code}

\begin{code}
fmap-pure-fun : (Γ : Ctx tot) (A B : Ty tot) 
          → (f : Tm Γ (▻ (A ⇒ B))) (t : Tm Γ A)
          → def-eq Γ
                   (▻ B)
                   (fmap Γ A B f (pure Γ A t))
                   (fmap Γ (A ⇒ B) B
                         (pure Γ ((A ⇒ B) ⇒ B)
                               (lambda Γ (A ⇒ B) B
                                       (sem-app-map (Γ ,, (A ⇒ B)) A B
                                            (var Γ (A ⇒ B))
                                            (weaken Γ (A ⇒ B) A t))))
                          f)
fmap-pure-fun Γ A B (f , p) (t , q) i γ =
  Σ≡-uip
    (funext (λ { [ _ ] → funext (λ { [ _ ] → uip })}))
    (funext (λ { [ j ] → cong (λ a → proj₁ (proj₁ (f i γ) [ j ]) j (t j a)) (sym (MorId Γ))}))
\end{code}
