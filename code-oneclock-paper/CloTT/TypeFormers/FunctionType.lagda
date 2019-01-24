\AgdaHide{
\begin{code}
module CloTT.TypeFormers.FunctionType where

open import Data.Product
open import Prelude
open import Presheaves
open import CloTT.Structure

open PSh
open ExpObj
open NatTrans
\end{code}
}

\begin{code}
_⇒_ : {Δ : ClockContext} (A B : Ty Δ) → Ty Δ
\end{code}

\AgdaHide{
\begin{code}
_⇒_ {∅} A B = A → B
_⇒_ {κ} A B = Exp A B
\end{code}
}

\AgdaHide{
\begin{code}
sem-lambda : {Δ : ClockContext} (Γ : Ctx Δ) (A B : Ty Δ) (t : Tm (Γ ,, A) B)
  → Tm Γ (A ⇒ B)
sem-lambda {∅} Γ A B t x y = t (x , y)
fun (nat-map (sem-lambda {κ} Γ A B t) i x) j z = nat-map t j (Mor Γ i j x , z)
funcom (nat-map (sem-lambda {κ} Γ A B t) i x) j k z =
  begin
    Mor B j k (nat-map t j (Mor Γ i j x , z))
  ≡⟨ nat-com t j k (Mor Γ i j x , z) ⟩
    nat-map t k (Mor (Γ ,, A) j k (Mor Γ i j x , z))
  ≡⟨ cong (λ z → nat-map t k (z , _)) (sym (MorComp Γ)) ⟩
    nat-map t k (Mor Γ i k x , Mor A j k z)
  ∎
nat-com (sem-lambda {κ} Γ A B t) i j x = funeq (λ k z → cong (λ z → nat-map t k (z , _)) (MorComp Γ))
\end{code}

\begin{code}
sem-app : {Δ : ClockContext} (Γ : Ctx Δ) (A B : Ty Δ)
      (f : Tm Γ (A ⇒ B))
  → Tm (Γ ,, A) B
sem-app {∅} Γ A B f (x , y) = f x y
nat-map (sem-app {κ} Γ A B f) i (x , y) = fun (nat-map f i x) i y
nat-com (sem-app {κ} Γ A B f) i j (x , y) =
  begin
    Mor B i j (fun (nat-map f i x) i y)
  ≡⟨ funcom (nat-map f i x) i j y ⟩
    fun (nat-map f i x) j (Mor A i j y)
  ≡⟨ cong (λ z → fun z j (Mor A i j y)) (nat-com f i j x) ⟩
    fun (nat-map f j (Mor Γ i j x)) j (Mor A i j y)
  ∎
\end{code}

\begin{code}
sem-app-map : {Δ : ClockContext} (Γ : Ctx Δ) (A B : Ty Δ) → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
sem-app-map Γ A B f t = sem-sub Γ (Γ ,, A) B (sem-app Γ A B f) (sem-subst-tm Γ Γ A (sem-idsub Γ) t)
\end{code}
}
