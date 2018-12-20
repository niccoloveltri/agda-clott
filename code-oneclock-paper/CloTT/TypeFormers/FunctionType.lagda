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
      (f : Tm Γ (A ⇒ B))
  → Tm (Γ ,, A) B
app {set} Γ A B f (x , y) = f x y
proj₁ (app {tot} Γ A B (f , p)) i (x , y) =  proj₁(f i x) i y
proj₂ (app {tot} Γ A B (f , p)) i j (x , y) =
  begin
    Mor B i j (proj₁ (f i x) i y)
  ≡⟨ proj₂ (f i x) i j y ⟩
    proj₁ (f i x) j (Mor A i j y)
  ≡⟨ cong (λ z → proj₁ z j (Mor A i j y)) (p i j x) ⟩
    proj₁ (f j (Mor Γ i j x)) j (Mor A i j y)
  ∎
\end{code}

\AgdaHide{
\begin{code}
sem-app-map : {b : tag} (Γ : Ctx b) (A B : Ty b) → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
sem-app-map {b} Γ A B f t = sem-sub Γ (Γ ,, A) B (app Γ A B f) (sem-subst-tm Γ Γ A (sem-idsub Γ) t)
\end{code}
}
