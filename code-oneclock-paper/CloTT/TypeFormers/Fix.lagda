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
open ►Obj
\end{code}
}

\begin{code}
dfix₁ : (A : Ty tot) (i : Size) → ExpObj (► A) A i → ►Obj A i
►cone (dfix₁ A i (f , p)) [ j ] = f j (dfix₁ A j (f , p))
\end{code}

\AgdaHide{
\begin{code}
►com (dfix₁ A i (f , p)) [ j ] [ k ] = 
  begin
    Mor A j k (f j (dfix₁ A j (f , p)))
  ≡⟨ p j k (dfix₁ A j (f , p)) ⟩
    f k (►Mor A j k (dfix₁ A j (f , p)))
  ≡⟨ cong (f k) (►eq (λ {_ → refl})) ⟩
    f k (dfix₁ A k (f , p))
  ∎
\end{code}
}

\begin{code}
dfix : (Γ : Ctx tot) (A : Ty tot) (f : Tm Γ (► A ⇒ A)) → Tm Γ (► A)
proj₁ (dfix Γ A (f , p)) i γ = dfix₁ A i (f i γ)
\end{code}

\AgdaHide{
\begin{code}
proj₂ (dfix Γ A (f , p)) i j γ = ►eq (λ {k → cong (λ a → proj₁ a k (dfix₁ A k (proj₁ a , proj₂ a))) (p i j γ)})
\end{code}
}

By applying \AB{f} to \F{dfix}, we can obtain the required fixpoint operations \F{fix}.

\begin{code}
fix : (Γ : Ctx tot) (A : Ty tot) (f : Tm Γ (► A ⇒ A)) → Tm Γ A
\end{code}

\AgdaHide{
\begin{code}
fix Γ A f = sem-app-map Γ (► A) A f (dfix Γ A f)
\end{code}
}
