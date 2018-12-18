\AgdaHide{
\begin{code}
module CloTT.TypeFormers.FunctionType where

open import Data.Product
open import Prelude
open import Presheaves
open import CloTT.Structure

open PSh
\end{code}
}

\begin{code}
_⇒_ : {b : tag} (A B : Ty b) → Ty b
_⇒_ {set} A B = A → B
_⇒_ {tot} A B = Exp A B
\end{code}

\begin{code}
lambda : {b : tag} (Γ : Ctx b) (A B : Ty b) (t : Tm (Γ ,, A) B)
  → Tm Γ (A ⇒ B)
lambda {set} Γ A B t x y = t (x , y)
proj₁ (proj₁ (lambda {tot} Γ A B (t , p)) i x) j z = t j (Mor Γ i j x , z)
proj₂ (proj₁ (lambda {tot} Γ A B (t , p)) i x) j k y =
  begin
    Mor B j k (t j (Mor Γ i j x , y))
  ≡⟨ p j k (Mor Γ i j x , y) ⟩
    t k (Mor (Γ ,, A) j k (Mor Γ i j x , y))
  ≡⟨ cong (λ z → t k (z , _)) (sym (MorComp Γ)) ⟩
    t k (Mor Γ i k x , Mor A j k y)
  ∎
proj₂ (lambda {tot} Γ A B (t , p)) i j x =
  Σ≡-uip
    (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
    (funext (λ k → (funext (λ z → cong (λ z → t k (z , _)) (MorComp Γ)))))
\end{code}

\begin{code}
app : {b : tag} (Γ : Ctx b) (A B : Ty b)
      (f : Tm Γ (A ⇒ B)) (t : Tm Γ A)
  → Tm Γ B
app {set} Γ A B f t x = f x (t x)
proj₁ (app {tot} Γ A B (f , p) (t , q)) i x =
  let (f' , _) = f i x in
  f' _ (t i x)
proj₂ (app {tot} Γ A B (f , p) (t , q)) i j x =
  let (f' , p') = f i x in
  begin
    Mor B i j (proj₁ (f i x) _ (t i x))
  ≡⟨ p' i j (t i x) ⟩
    proj₁ (f i x) j (Mor A i j (t i x))
  ≡⟨ cong₂ (λ z g → proj₁ g _ z) (q i j x) (p i j x) ⟩
    proj₁ (f j (Mor Γ i j x)) _ (t j (Mor Γ i j x))
  ∎
\end{code}

\begin{code}
beta : {b : tag} {Γ : Ctx b} {A B : Ty b} (t : Tm (Γ ,, A) B) (x : Tm Γ A)
     → def-eq Γ B
              (app Γ A B (lambda Γ A B t) x)
              (subst-Tm Γ A B t x)
beta {set} t x _ = refl
beta {tot} {Γ} (t , p) (x , q) Δ z =
  begin
    t Δ (Mor Γ Δ Δ z , x Δ z)
  ≡⟨ cong (λ z → t Δ (z , _)) (MorId Γ) ⟩
    t Δ (z , x Δ z)
  ∎
\end{code}

\begin{code}
eta : {b : tag} {Γ : Ctx b} {A B : Ty b} (t : Tm Γ (A ⇒ B))
  → def-eq Γ (A ⇒ B)
           (lambda Γ A B (app (Γ ,, A) A B (weaken Γ A (A ⇒ B) t) (var Γ A)))
           t
eta {set} t x = refl
eta {tot} (t , p) Δ x =
  Σ≡-uip
    (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
    (funext (λ Δ' → funext (λ z → sym (cong (λ h → proj₁ h _ z) (p Δ Δ' x)))))
\end{code}

\begin{code}
id-tm : {b : tag} (Γ : Ctx b) (A : Ty b) → Tm Γ (A ⇒ A)
id-tm Γ A = lambda _ _ _ (var _ _)
\end{code}

\begin{code}
comp-tm : {b : tag} (Γ : Ctx b) (A B C : Ty b)
  → Tm Γ ((B ⇒ C) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
comp-tm Γ A B C = lambda _ _ _
                         (lambda _ _ _
                                 (lambda _ _ _
                                         (app _ _ _
                                              (weaken _ _ _
                                                      (weaken _ _ _
                                                              (var _ _)))
                                              (app _ _ _
                                                   (weaken _ _ _
                                                           (var _ _))
                                                           (var _ _)))))
\end{code}
