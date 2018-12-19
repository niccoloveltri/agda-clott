\AgdaHide{
\begin{code}
module CloTT.TypeFormers.Fix where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.LaterType
open import CloTT.TypeFormers.FunctionType

open PSh
\end{code}
}

\begin{code}
dfix₁ : (A : Ty tot) (i : Size) → ExpObj (▻ A) A i → ▻Obj A i
proj₁ (dfix₁ A i (f , p)) [ j ] = f j (dfix₁ A j (f , p))
proj₂ (dfix₁ A i (f , p)) [ j ] [ k ] = 
  begin
    Mor A j k (f j (dfix₁ A j (f , p)))
  ≡⟨ p j k (dfix₁ A j (f , p)) ⟩
    f k (▻Mor A j k (dfix₁ A j (f , p)))
  ≡⟨ cong (f k) (Σ≡-uip (funext (λ { [ j ] → funext (λ { [ k ] → uip }) })) (funext (λ { [ _ ] → refl}))) ⟩
    f k (dfix₁ A k (f , p))
  ∎
\end{code}

\begin{code}
dfix : (Γ : Ctx tot) (A : Ty tot) (f : Tm Γ (▻ A ⇒ A)) → Tm Γ (▻ A)
proj₁ (dfix Γ A (f , _)) i γ = dfix₁ A i (f i γ)
proj₂ (dfix Γ A (f , p)) i j γ =
  Σ≡-uip (funext (λ { [ j ] → funext (λ { [ k ] → uip }) }))
         (funext (λ { [ k ] → cong (λ a → proj₁ a k (dfix₁ A k (proj₁ a , proj₂ a))) (p i j γ) }))
\end{code}

\begin{code}
fix : (Γ : Ctx tot) (A : Ty tot) (f : Tm Γ (▻ A ⇒ A)) → Tm Γ A
fix Γ A f = sem-app-map Γ (▻ A) A f (dfix Γ A f)
\end{code}

\begin{code}
dfix-eq : (Γ : Ctx tot) (A : Ty tot) (f : Tm Γ (▻ A ⇒ A))
  → def-eq {tot} Γ (▻ A) (dfix Γ A f) (pure Γ A (fix Γ A f))
dfix-eq Γ A (f , p) i γ =
  Σ≡-uip
    (funext (λ { [ j ] → funext (λ { [ k ] → uip }) }))
    (funext (λ { [ j ] → cong (λ a → proj₁ a j (dfix₁ A j (proj₁ a , proj₂ a))) (p i j γ)}))
\end{code}

\begin{code}
fix-eq : (Γ : Ctx tot) (A : Ty tot) (f : Tm Γ (▻ A ⇒ A))
  → def-eq Γ A
           (fix Γ A f)
           (sem-app-map Γ (▻ A) A f (pure Γ A (fix Γ A f)))
fix-eq Γ A f i x = cong (proj₁ (proj₁ f i x) i) (dfix-eq Γ A f i x)
\end{code}
