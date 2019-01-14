\AgdaHide{
\begin{code}
module GuardedTT where

open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Level renaming (suc to lsuc;_⊔_ to _l⊔_)
open import Prelude
open import Prelude.Syntax
open import Presheaves
open import CloTT
\end{code}
}

\begin{code}
record interpret-syntax {ℓ₁ ℓ₂} : Set (lsuc (ℓ₁ l⊔ ℓ₂)) where
\end{code}

\AgdaHide{
\begin{code}
  field
    semType : ClockContext → Set ℓ₁
    semContext : ClockContext → Set ℓ₁
    semSubst : ∀ {Δ} → semContext Δ → semContext Δ → Set ℓ₂
    semTerm : ∀ {Δ} → semContext Δ → semType Δ → Set ℓ₂
    _[_sem∼_] : ∀ {Δ} {Γ : semContext Δ} {A : semType Δ}
      → semTerm Γ A → semTerm Γ A → Set ℓ₂
    _[_sem≈_] : ∀ {Δ} {Γ₁ Γ₂ : semContext Δ} → semSubst Γ₁ Γ₂ → semSubst Γ₁ Γ₂ → Set ℓ₂
    _⟦_⟧Type : ∀ {Δ} → Type Δ → semType Δ
    _⟦_⟧Ctx : ∀ {Δ} → Context Δ → semContext Δ
    _⟦_⟧Subst : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} → Subst Γ₁ Γ₂ → semSubst (_⟦_⟧Ctx Γ₁) (_⟦_⟧Ctx Γ₂)
    _⟦_⟧Tm : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} → Term Γ A → semTerm (_⟦_⟧Ctx Γ) (_⟦_⟧Type A)
    _⟦_⟧∼ : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} {t t' : Term Γ A}
      → t ∼ t' → _[_sem∼_] (_⟦_⟧Tm t) (_⟦_⟧Tm t')
    _⟦_⟧≈ : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {s s' : Subst Γ₁ Γ₂}
      → s ≈ s' → _[_sem≈_] (_⟦_⟧Subst s) (_⟦_⟧Subst s')
\end{code}
}

\AgdaHide{
\begin{code}
open interpret-syntax
\end{code}
}

\begin{code}
initial-interpretation : interpret-syntax
\end{code}

\AgdaHide{
\begin{code}
semType initial-interpretation = Type
semContext initial-interpretation = Context
semSubst initial-interpretation = Subst
semTerm initial-interpretation = Term
_[_sem∼_] initial-interpretation = _∼_
_[_sem≈_] initial-interpretation = _≈_
_⟦_⟧Type initial-interpretation = id
_⟦_⟧Ctx initial-interpretation = id
_⟦_⟧Subst initial-interpretation = id
_⟦_⟧Tm initial-interpretation = id
_⟦_⟧∼ initial-interpretation = id
_⟦_⟧≈ initial-interpretation = id
\end{code}
}

\begin{code}
bool : Type ∅
bool = 𝟙 ⊞ 𝟙

TRUE : Term • bool
TRUE = in₁ 𝟙 tt

FALSE : Term • bool
FALSE = in₂ 𝟙 tt
\end{code}

\begin{code}
consistent : ∀ {ℓ₁ ℓ₂} → interpret-syntax {ℓ₁} {ℓ₂} → Set ℓ₂
consistent sem = sem [ sem ⟦ TRUE ⟧Tm sem∼ sem ⟦ FALSE ⟧Tm ] → ⊥
\end{code}

\AgdaHide{
\begin{code}
sub-π₁ : {Δ : ClockContext} {Γ₁ Γ₂ : Context Δ} {A : Type Δ} {B : Type Δ} (t : Term Γ₁ (A ⊠ B)) (s : Subst Γ₂ Γ₁)
  → sub (π₁ t) s ∼ π₁ (sub t s)
sub-π₁ t s =
  trans∼ (sym∼ (⊠-β₁ (sub (π₁ t) s) (sub (π₂ t) s)))
         (cong-π₁ (trans∼ (sym∼ (sub-[ (π₁ t) & (π₂ t) ] s)) (cong-sub (⊠-η t) refl≈)))

sub-π₂ : {Δ : ClockContext} {Γ₁ Γ₂ : Context Δ} {A : Type Δ} {B : Type Δ} (t : Term Γ₁ (A ⊠ B)) (s : Subst Γ₂ Γ₁)
  → sub (π₂ t) s ∼ π₂ (sub t s)
sub-π₂ t s =
  trans∼ (sym∼ (⊠-β₂ (sub (π₁ t) s) (sub (π₂ t) s)))
         (cong-π₂ (trans∼ (sym∼ (sub-[ (π₁ t) & (π₂ t) ] s)) (cong-sub (⊠-η t) refl≈)))

sub-appTm : {Δ : ClockContext} {Γ₁ Γ₂ : Context Δ} {A : Type Δ} {B : Type Δ} (t : Term Γ₁ (A ⟶ B)) (s : Subst Γ₂ Γ₁)
  → sub (appTm t) (weakenSA A s) ∼ appTm (sub t s)
sub-appTm t s =
  trans∼ (sym∼ (λ-β _))
         (trans∼ (cong-appTm (sym∼ (sub-lambdaTm (appTm t) s)))
                 (cong-appTm (cong-sub (λ-η t) refl≈)))

sub-unbox-q : {Γ₁ Γ₂ : Context ∅} {A : Type κ} (t : Term Γ₁ (□ A)) (s : Subst Γ₂ Γ₁)
  → sub (unbox-q t) (weakenS s) ∼ unbox-q (sub t s)
sub-unbox-q t s =
  trans∼ (sym∼ (□-β (sub (unbox-q t) (weakenS s))))
         (cong-unbox-q (trans∼ (sym∼ (sub-box-q (unbox-q t) s)) (cong-sub (□-η t) refl≈)))

sub-↓ : {Γ₁ Γ₂ : Context ∅} {A : Type ∅} (t : Term (⇑ Γ₁) (⇑ A)) (s : Subst Γ₂ Γ₁)
  → sub (↓ t) s ∼ ↓(sub t (weakenS s))
sub-↓ t s =
  trans∼ (sym∼ (⇡-β (sub (↓ t) s)))
         (cong-↓ (trans∼ (sym∼ (sub-⇡ (↓ t) s)) (cong-sub (⇡-η t) refl≈)))

sub-tt : {Γ₁ Γ₂ : Context ∅} (s : Subst Γ₂ Γ₁) → sub tt s ∼ tt
sub-tt s = 𝟙-η (sub tt s)
\end{code}
}

\begin{code}
sem : interpret-syntax
\end{code}

\AgdaHide{
\begin{code}
semType sem = Ty
semContext sem = Ctx
semSubst sem = sem-subst
semTerm sem = Tm
_[_sem∼_] sem = def-eq _ _
_[_sem≈_] sem = subst-eq _ _
_⟦_⟧Type sem = ⟦_⟧A
_⟦_⟧Ctx sem = ⟦_⟧Γ
_⟦_⟧Subst sem = ⟦_⟧sub
_⟦_⟧Tm sem = ⟦_⟧tm
_⟦_⟧∼ sem = ⟦_⟧tm-eq
_⟦_⟧≈ sem = ⟦_⟧sub-eq

sem-consistent-help : ⊤ ⊎ ⊤ → Set
sem-consistent-help (inj₁ x) = ⊤
sem-consistent-help (inj₂ y) = ⊥
\end{code}
}

\begin{code}
sem-consistent : consistent sem
\end{code}

\AgdaHide{
\begin{code}
sem-consistent p = subst sem-consistent-help (p ⊤.tt) ⊤.tt
\end{code}
}

\begin{code}
syntax-consistent : consistent initial-interpretation
syntax-consistent p = sem-consistent (sem ⟦ p ⟧∼)
\end{code}
