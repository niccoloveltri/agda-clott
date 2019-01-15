\AgdaHide{
\begin{code}
module CloTT.Structure.Subst where

open import Data.Unit
open import Data.Product
open import Prelude
open import CloTT.Structure.Contexts
open import CloTT.Structure.ContextOperations
open import CloTT.Structure.Types
open import CloTT.Structure.Terms

open PSh
open NatTrans
\end{code}
}

The type theory we study, has explicit substitutions and we must also provide an interpretation for these.
Substitutions are maps between contexts.
Again there are two cases.
If the clock context is empty, then we just use functions.
If we have one clock variable, then we use  natural transformations.

\begin{code}
sem-subst : {Δ : ClockContext} → Ctx Δ → Ctx Δ → Set
sem-subst {∅} Γ₁ Γ₂ = Γ₁ → Γ₂
sem-subst {κ} Γ₁ Γ₂ = NatTrans Γ₁ Γ₂
\end{code}

Next we define the interpretation of operations on substitutions.
These all are defined in the expected way.
For the precise definitions, we refer the reader to the formalization.

\AgdaHide{
As an example, we show how an explicit substitution gives rise to an actual one.
We only give the component map and not the proof of naturality.

\begin{code}
sem-sub : {Δ : ClockContext} (Γ₁ Γ₂ : Ctx Δ) (A : Ty Δ)
  → Tm Γ₂ A → sem-subst Γ₁ Γ₂ → Tm Γ₁ A
sem-sub {∅} Γ₁ Γ₂ A t α x = t(α x)
nat-map (sem-sub {κ} Γ₁ Γ₂ A t α) i x = nat-map t i (nat-map α i x)
\end{code}
\begin{code}
nat-com (sem-sub {κ} Γ₁ Γ₂ A t α) i j x =
  begin
    Mor A i j (nat-map t i (nat-map α i x))
  ≡⟨ nat-com t i j (nat-map α i x) ⟩
    nat-map t j (Mor Γ₂ i j (nat-map α i x))
  ≡⟨ cong (nat-map t j) (nat-com α i j x) ⟩
    nat-map t j (nat-map α j (Mor Γ₁ i j x))
  ∎
\end{code}
}

\AgdaHide{
\begin{code}
sem-idsub : {Δ : ClockContext} (Γ : Ctx Δ) → sem-subst Γ Γ
sem-idsub {∅} Γ x = x
nat-map (sem-idsub {κ} Γ) i x = x
nat-com (sem-idsub {κ} Γ) i j x = refl
\end{code}

\begin{code}
sem-ε : {Δ : ClockContext} (Γ : Ctx Δ) → sem-subst Γ (∙ Δ)
sem-ε {∅} Γ x = tt
nat-map (sem-ε {κ} Γ) i x = tt
nat-com (sem-ε {κ} Γ) i j x = refl
\end{code}

\begin{code}
sem-subcomp : {Δ : ClockContext} (Γ₁ Γ₂ Γ₃ : Ctx Δ) → sem-subst Γ₂ Γ₃ → sem-subst Γ₁ Γ₂ → sem-subst Γ₁ Γ₃
sem-subcomp {∅} Γ₁ Γ₂ Γ₃ α β x = α(β x)
nat-map (sem-subcomp {κ} Γ₁ Γ₂ Γ₃ α β) i x = nat-map α i (nat-map β i x) 
nat-com (sem-subcomp {κ} Γ₁ Γ₂ Γ₃ α β) i j x =
  begin
    Mor Γ₃ i j (nat-map α i (nat-map β i x))
  ≡⟨ nat-com α i j (nat-map β i x) ⟩
    nat-map α j (Mor Γ₂ i j (nat-map β i x))
  ≡⟨ cong (nat-map α j) (nat-com β i j x) ⟩
    nat-map α j (nat-map β j (Mor Γ₁ i j x))
  ∎
\end{code}

\begin{code}
sem-subst-tm : {Δ : ClockContext} (Γ₁ Γ₂ : Ctx Δ) (A : Ty Δ) → sem-subst Γ₁ Γ₂ → Tm Γ₁ A → sem-subst Γ₁ (Γ₂ ,, A)
sem-subst-tm {∅} Γ₁ Γ₂ A α t x = α x , t x
nat-map (sem-subst-tm {κ} Γ₁ Γ₂ A α t) i x = nat-map α i x , nat-map t i x
nat-com (sem-subst-tm {κ} Γ₁ Γ₂ A α t) i j x =
  begin
    (Mor Γ₂ i j (nat-map α i x) , Mor A i j (nat-map t i x))
  ≡⟨ cong (λ z → (_ , z)) (nat-com t i j x) ⟩
    (Mor Γ₂ i j (nat-map α i x) , nat-map t j (Mor Γ₁ i j x))
  ≡⟨ cong (λ z → (z , _)) (nat-com α i j x) ⟩
    (nat-map α j (Mor Γ₁ i j x) , nat-map t j (Mor Γ₁ i j x))
  ∎
\end{code}

\begin{code}
sem-subpr : {Δ : ClockContext} (Γ₁ Γ₂ : Ctx Δ) (A : Ty Δ) → sem-subst Γ₁ (Γ₂ ,, A) → sem-subst Γ₁ Γ₂
sem-subpr {∅} Γ₁ Γ₂ A α z = proj₁ (α z)
nat-map (sem-subpr {κ} Γ₁ Γ₂ A α) i x = proj₁ (nat-map α i x)
nat-com (sem-subpr {κ} Γ₁ Γ₂ A α) i j x = cong proj₁ (nat-com α i j x)
\end{code}
}
