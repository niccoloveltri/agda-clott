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

\begin{code}
dfix-un : (Γ : Ctx tot) (A : Ty tot) (f : Tm Γ (▻ A ⇒ A)) (u : Tm Γ A) (i : Size) (x : Obj Γ i)
  → def-eq Γ A (sem-app-map Γ (▻ A) A f (pure Γ A u)) u
  → dfix₁ A i (proj₁ f i x) ≡ proj₁ (pure Γ A u) i x
dfix-un Γ A (f , p) (u , q) i x r =
  Σ≡-uip
    (funext (λ { [ j ] → funext (λ { [ k ] → uip }) }))
    (funext (λ {[ j ] →
      begin
        proj₁ (f i x) j (dfix₁ A j (proj₁ (f i x) , proj₂ (f i x)))
      ≡⟨ cong (λ z → proj₁ z j (dfix₁ A j z)) (p i j x) ⟩
        proj₁ (f j (Mor Γ i j x)) j (dfix₁ A j (f j (Mor Γ i j x)))
      ≡⟨ cong (proj₁ (f j (Mor Γ i j x)) j) (dfix-un Γ A (f , p) (u , q) j (Mor Γ i j x) r) ⟩
        proj₁ (f j (Mor Γ i j x)) j (proj₁ (pure Γ A (u , q)) j (Mor Γ i j x))
      ≡⟨ r j (Mor Γ i j x) ⟩
        u j (Mor Γ i j x)
      ∎
    })) -- trans {!dfix-un Γ A (f , p) (u , q) j (Mor Γ i j x) r!} (r j (Mor Γ i j x))}))

fix-un : (Γ : Ctx tot) (A : Ty tot) (f : Tm Γ (▻ A ⇒ A)) (u : Tm Γ A)
  → def-eq Γ A (sem-app-map Γ (▻ A) A f (pure Γ A u)) u
  → def-eq Γ A (fix Γ A f) u
fix-un Γ A f u p i x =
  begin
    proj₁ (fix Γ A f) i x
  ≡⟨ cong (λ z → proj₁ (proj₁ f i x) i z) (dfix-un Γ A f u i x p) ⟩
    proj₁ (sem-app-map Γ (▻ A) A f (pure Γ A u)) i x
  ≡⟨ p i x ⟩
    proj₁ u i x
  ∎
\end{code}
