\AgdaHide{
\begin{code}
module CloTT.InterpretSyntax where

open import Data.Product
open import Data.Unit
open import Prelude
open import Prelude.Syntax
open import Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers

open PSh
\end{code}
}

\begin{code}
⟦_⟧Δ : ClockContext → tag
⟦ ∅ ⟧Δ = set
⟦ κ ⟧Δ = tot

⟦_⟧A : {Δ : ClockContext} → Type Δ → Ty ⟦ Δ ⟧Δ
⟦ 𝟙 ⟧A = Unit
⟦ A ⊞ B ⟧A = ⟦ A ⟧A ⊕ ⟦ B ⟧A
⟦ A ⊠ B ⟧A = ⟦ A ⟧A ⊗ ⟦ B ⟧A
⟦ A ⟶ B ⟧A = ⟦ A ⟧A ⇒ ⟦ B ⟧A
⟦ weakenT A ⟧A = WC ⟦ A ⟧A
⟦ later A ⟧A = ▻(⟦ A ⟧A)
⟦ clock-q A ⟧A = □(⟦ A ⟧A)

⟦_⟧Γ : {Δ : ClockContext} → Context Δ → Ctx ⟦ Δ ⟧Δ
⟦ • ⟧Γ = ∙ _
⟦ Γ , A ⟧Γ = (⟦ Γ ⟧Γ) ,, ⟦ A ⟧A
⟦ weakenC Γ ⟧Γ = WC ⟦ Γ ⟧Γ

mutual
  ⟦_⟧sub : {Δ : ClockContext} {Γ Γ' : Context Δ} → Subst Γ Γ' → sem-subst ⟦ Γ ⟧Γ ⟦ Γ' ⟧Γ
  ⟦ ε Γ ⟧sub = sem-ε ⟦ Γ ⟧Γ
  ⟦ idsub Γ ⟧sub = sem-idsub ⟦ Γ ⟧Γ
  ⟦ s ,s x ⟧sub = sem-subst-tm _ _ _ ⟦ s ⟧sub ⟦ x ⟧tm
  ⟦ s o s' ⟧sub = sem-subcomp _ _ _ ⟦ s ⟧sub ⟦ s' ⟧sub
  ⟦ pr {_} {Γ} {Γ'} {A} s ⟧sub = sem-subpr ⟦ Γ ⟧Γ ⟦ Γ' ⟧Γ ⟦ A ⟧A ⟦ s ⟧sub
  proj₁ ⟦ weakenS s ⟧sub i = ⟦ s ⟧sub
  proj₂ ⟦ weakenS s ⟧sub i j x = refl
  proj₁ ⟦ •-to-weaken ⟧sub i tt = tt
  proj₂ ⟦ •-to-weaken ⟧sub i j x = refl
  proj₁ ⟦ ,-weaken Γ A ⟧sub i x = x
  proj₂ ⟦ ,-weaken Γ A ⟧sub i j x = refl
  
  ⟦_⟧tm : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} → Term Γ A → Tm ⟦ Γ ⟧Γ ⟦ A ⟧A
  ⟦ sub t s ⟧tm = sem-sub _ _ _ ⟦ t ⟧tm ⟦ s ⟧sub
  ⟦ varTm Γ A ⟧tm = var ⟦ Γ ⟧Γ ⟦ A ⟧A
  ⟦ tt ⟧tm = ⋆ _
  ⟦ unit-rec t ⟧tm = Unit-rec _ _ ⟦ t ⟧tm
  ⟦ in₁ B t ⟧tm = inl _ _ ⟦ B ⟧A ⟦ t ⟧tm
  ⟦ in₂ A t ⟧tm = inr _ ⟦ A ⟧A _ ⟦ t ⟧tm
  ⟦ ⊞rec C l r ⟧tm = sum-rec _ _ _ ⟦ C ⟧A ⟦ l ⟧tm ⟦ r ⟧tm
  ⟦ [ t₁ & t₂ ] ⟧tm = pair _ _ _ ⟦ t₁ ⟧tm ⟦ t₂ ⟧tm
  ⟦ π₁ t ⟧tm = pr₁ _ _ _ ⟦ t ⟧tm
  ⟦ π₂ t ⟧tm = pr₂ _ _ _ ⟦ t ⟧tm
  ⟦ lambdaTm t ⟧tm = lambda _ _ _ ⟦ t ⟧tm
  ⟦ appTm f ⟧tm = app _ _ _ ⟦ f ⟧tm
  ⟦ ⇡ t ⟧tm = WC-fun _ _ ⟦ t ⟧tm
  ⟦ ↓ t ⟧tm = WC-unfun _ _ ⟦ t ⟧tm
  ⟦ box-q {Γ} {A} t ⟧tm = box ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ t ⟧tm
  ⟦ unbox-q {Γ} {A} t ⟧tm = unbox ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ t ⟧tm
  ⟦ next {Γ} {A} t ⟧tm = pure ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ t ⟧tm
  ⟦ _⊛_ {Γ} {A} {B} f t ⟧tm = fmap ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ B ⟧A ⟦ f ⟧tm ⟦ t ⟧tm
  ⟦ fix-tm {Γ} {A} f ⟧tm = fix ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ f ⟧tm
  ⟦ force {Γ} {A} t ⟧tm = force-tm ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ t ⟧tm
  ⟦ □const A ⟧tm = □const-tm _ ⟦ A ⟧A
  ⟦ □sum A B ⟧tm = □sum-tm _ ⟦ A ⟧A ⟦ B ⟧A
\end{code}
