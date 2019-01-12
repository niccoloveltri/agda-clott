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
open ExpObj
\end{code}
}

\begin{code}
dfix₁ : (A : Ty tot) (i : Size) → ExpObj (► A) A i → ►Obj A i
►cone (dfix₁ A i f) [ j ] = fun f j (dfix₁ A j f)
\end{code}

\AgdaHide{
\begin{code}
►com (dfix₁ A i f) [ j ] [ k ] = 
  begin
    Mor A j k (fun f j (dfix₁ A j f))
  ≡⟨ funcom f j k (dfix₁ A j f) ⟩
    fun f k (►Mor A j k (dfix₁ A j f))
  ≡⟨ cong (fun f k) (►eq (λ {_ → refl})) ⟩
    fun f k (dfix₁ A k f)
  ∎
\end{code}
}

\begin{code}
dfix : (Γ : Ctx tot) (A : Ty tot) (f : Tm Γ (► A ⇒ A)) → Tm Γ (► A)
proj₁ (dfix Γ A (f , p)) i γ = dfix₁ A i (f i γ)
\end{code}

\AgdaHide{
\begin{code}
proj₂ (dfix Γ A (f , p)) i j γ = ►eq (λ {k → cong (λ a → fun a k (dfix₁ A k a)) (p i j γ)})
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
