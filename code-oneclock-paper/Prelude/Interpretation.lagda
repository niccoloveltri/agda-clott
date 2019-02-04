\AgdaHide{
\begin{code}
module Prelude.Interpretation where

open import Prelude.Syntax
\end{code}
}

Now let us put everything together and define the notion of an interpretation of \GTT.
To give an interpretation, one must give a type of semantical types, contexts, terms, substitutions, and functions mapping the syntactic objects to their semantical counterparts.
In addition, definitional equality is interpreted as a relation on terms which includes the relation \D{∼} defined in \Cref{sec:syntax}, and the same is be done for substitutions.
We define a record containing all this data, whose type declaration is given as

\begin{code}
record interpret-syntax : Set₂ where
  field
    semTy : ClockCtx → Set₁
    _⟦_⟧Ty : ∀ {Δ} → Ty Δ → semTy Δ
\end{code}

\AgdaHide{
\begin{code}
    semCtx : ClockCtx → Set₁
    semTm : ∀ {Δ} → semCtx Δ → semTy Δ → Set
    semSub : ∀ {Δ} → semCtx Δ → semCtx Δ → Set
    _[_sem∼_] : ∀ {Δ} {Γ : semCtx Δ} {A : semTy Δ}
      → semTm Γ A → semTm Γ A → Set
    _[_sem≈_] : ∀ {Δ} {Γ₁ Γ₂ : semCtx Δ} → semSub Γ₁ Γ₂ → semSub Γ₁ Γ₂ → Set
    _⟦_⟧Ctx : ∀ {Δ} → Ctx Δ → semCtx Δ
    _⟦_⟧Tm : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} → Tm Γ A → semTm (_⟦_⟧Ctx Γ) (_⟦_⟧Ty A)
    _⟦_⟧Sub : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} → Sub Γ₁ Γ₂ → semSub (_⟦_⟧Ctx Γ₁) (_⟦_⟧Ctx Γ₂)
    _⟦_⟧∼ : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} {t t' : Tm Γ A}
      → t ∼ t' → _[_sem∼_] (_⟦_⟧Tm t) (_⟦_⟧Tm t')
    _⟦_⟧≈ : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} {s s' : Sub Γ₁ Γ₂}
      → s ≈ s' → _[_sem≈_] (_⟦_⟧Sub s) (_⟦_⟧Sub s')
\end{code}
}
