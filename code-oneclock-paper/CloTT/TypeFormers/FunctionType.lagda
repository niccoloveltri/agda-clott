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
_⇒_ : {b : ClockContext} (A B : Ty b) → Ty b
_⇒_ {∅} A B = A → B
_⇒_ {κ} A B = Exp A B
\end{code}

\begin{code}
lambda : {b : ClockContext} (Γ : Ctx b) (A B : Ty b) (t : Tm (Γ ,, A) B)
  → Tm Γ (A ⇒ B)
lambda {∅} Γ A B t x y = t (x , y)
fun (nat-map (lambda {κ} Γ A B t) i x) j z = nat-map t j (Mor Γ i j x , z)
funcom (nat-map (lambda {κ} Γ A B t) i x) j k z =
  begin
    Mor B j k (nat-map t j (Mor Γ i j x , z))
  ≡⟨ nat-com t j k (Mor Γ i j x , z) ⟩
    nat-map t k (Mor (Γ ,, A) j k (Mor Γ i j x , z))
  ≡⟨ cong (λ z → nat-map t k (z , _)) (sym (MorComp Γ)) ⟩
    nat-map t k (Mor Γ i k x , Mor A j k z)
  ∎
nat-com (lambda {κ} Γ A B t) i j x = funeq (λ k z → cong (λ z → nat-map t k (z , _)) (MorComp Γ))
\end{code}

\begin{code}
app : {b : ClockContext} (Γ : Ctx b) (A B : Ty b)
      (f : Tm Γ (A ⇒ B))
  → Tm (Γ ,, A) B
app {∅} Γ A B f (x , y) = f x y
nat-map (app {κ} Γ A B f) i (x , y) = fun (nat-map f i x) i y
nat-com (app {κ} Γ A B f) i j (x , y) =
  begin
    Mor B i j (fun (nat-map f i x) i y)
  ≡⟨ funcom (nat-map f i x) i j y ⟩
    fun (nat-map f i x) j (Mor A i j y)
  ≡⟨ cong (λ z → fun z j (Mor A i j y)) (nat-com f i j x) ⟩
    fun (nat-map f j (Mor Γ i j x)) j (Mor A i j y)
  ∎
\end{code}

\AgdaHide{
\begin{code}
sem-app-map : {b : ClockContext} (Γ : Ctx b) (A B : Ty b) → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
sem-app-map {b} Γ A B f t = sem-sub Γ (Γ ,, A) B (app Γ A B f) (sem-subst-tm Γ Γ A (sem-idsub Γ) t)
\end{code}
}
