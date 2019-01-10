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
record interpret-syntax {ℓCC}{ℓTy}{ℓCtx}{ℓSub}{ℓTm}{ℓ∼}{ℓ≈} : Set (lsuc (ℓCC l⊔ ℓTy l⊔ ℓCtx l⊔ ℓSub l⊔ ℓTm l⊔ ℓ∼ l⊔ ℓ≈)) where
  field
    semClockContext : Set ℓCC
    semType : semClockContext → Set ℓTy
    semContext : semClockContext → Set ℓCtx
    semSubst : {Δ : semClockContext} → semContext Δ → semContext Δ → Set ℓSub
    semTerm : {Δ : semClockContext} → semContext Δ → semType Δ → Set ℓTm
    _sem∼_ : {Δ : semClockContext} {Γ : semContext Δ} {A : semType Δ} → semTerm Γ A → semTerm Γ A → Set ℓ∼ -- \sim
    _sem≈_ : {Δ : semClockContext} {Γ Γ' : semContext Δ} → semSubst Γ Γ' → semSubst Γ Γ' → Set ℓ≈ -- ≈
    ⟦_⟧CCtx : ClockContext → semClockContext
    ⟦_⟧Type : {Δ : ClockContext} → Type Δ → semType ⟦ Δ ⟧CCtx
    ⟦_⟧Ctx : {Δ : ClockContext} → Context Δ → semContext ⟦ Δ ⟧CCtx
    ⟦_⟧Subst : {Δ : ClockContext} {Γ Γ' : Context Δ} → Subst Γ Γ' → semSubst ⟦ Γ ⟧Ctx ⟦ Γ' ⟧Ctx
    ⟦_⟧Tm : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} → Term Γ A → semTerm ⟦ Γ ⟧Ctx ⟦ A ⟧Type
    ⟦_⟧∼ : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {t t' : Term Γ A} → t ∼ t' → ⟦ t ⟧Tm sem∼ ⟦ t' ⟧Tm
    ⟦_⟧≈ : {Δ : ClockContext} {Γ Γ' : Context Δ} {s s' : Subst Γ Γ'} → s ≈ s' → ⟦ s ⟧Subst sem≈ ⟦ s' ⟧Subst
open interpret-syntax
\end{code}

\AgdaHide{
\begin{code}
initial-interpretation : interpret-syntax
initial-interpretation = record
  { semClockContext = ClockContext
  ; semType = Type
  ; semContext = Context
  ; semSubst = Subst
  ; semTerm = Term
  ; _sem∼_ = _∼_
  ; _sem≈_ = _≈_
  ; ⟦_⟧CCtx = id
  ; ⟦_⟧Type = id
  ; ⟦_⟧Ctx = id
  ; ⟦_⟧Subst = id
  ; ⟦_⟧Tm = id
  ; ⟦_⟧∼ = id
  ; ⟦_⟧≈ = id
  }

consistent : ∀ {ℓCC}{ℓTy}{ℓCtx}{ℓSub}{ℓTm}{ℓ≈} → interpret-syntax {ℓCC}{ℓTy}{ℓCtx}{ℓSub}{ℓTm}{_}{ℓ≈} → Set
consistent sem = (_sem∼_ sem (⟦ sem ⟧Tm TRUE) (⟦ sem ⟧Tm FALSE)) → ⊥
\end{code}
}

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

sub-unbox-q : {Γ₁ Γ₂ : Context ∅} {A : Type κ} (t : Term Γ₁ (clock-q A)) (s : Subst Γ₂ Γ₁)
  → sub (unbox-q t) (weakenS s) ∼ unbox-q (sub t s)
sub-unbox-q t s =
  trans∼ (sym∼ (□-β (sub (unbox-q t) (weakenS s))))
         (cong-unbox-q (trans∼ (sym∼ (sub-box-q (unbox-q t) s)) (cong-sub (□-η t) refl≈)))

sub-↓ : {Γ₁ Γ₂ : Context ∅} {A : Type ∅} (t : Term (weakenC Γ₁) (weakenT A)) (s : Subst Γ₂ Γ₁)
  → sub (↓ t) s ∼ ↓(sub t (weakenS s))
sub-↓ t s =
  trans∼ (sym∼ (⇡-β (sub (↓ t) s)))
         (cong-↓ (trans∼ (sym∼ (sub-⇡ (↓ t) s)) (cong-sub (⇡-η t) refl≈)))

sub-tt : {Γ₁ Γ₂ : Context ∅} (s : Subst Γ₂ Γ₁) → sub tt s ∼ tt
sub-tt s = 𝟙-η (sub tt s)
\end{code}
}

\AgdaHide{
\begin{code}
nat : Type ∅
nat = μ ((∁ 𝟙) ⊞ I)

Z : Term • nat
Z = cons _ (in₁ _ tt)

S : Term • (nat ⟶ nat)
S = lambdaTm (cons _ (in₂ _ (varTm • nat)))

stream' : Type ∅ → Type κ
stream' A = μ ((∁ (weakenT A)) ⊠ ► I)

stream : Type ∅ → Type ∅
stream A = clock-q (stream' A)

head : (A : Type ∅) → Term • (stream A ⟶ A)
head A = lambdaTm (↓ (sub (app-map (weakenTm _ _ _ (primrec _ (lambdaTm (π₁(π₁ (varTm _ _)))))) (varTm _ _))
                  ((pr (idsub (weakenC • , weakenT (clock-q (μ (∁ (weakenT A) ⊠ ► I))))) ,s sub (unbox-q (varTm • (stream A)))
                       (,-weaken • (clock-q (μ (∁ (weakenT A) ⊠ ► I))))) o weaken-, • (stream A))))

tail : (A : Type ∅) → Term • (stream A ⟶ stream A)
tail A = lambdaTm (force (box-q
                         (app-map (primrec ((∁ (weakenT A)) ⊠ ► I) {weakenC (• , stream A)} (lambdaTm (π₂(π₁(varTm _ _)))))
                                  (unbox-q (varTm _ _)))))
\end{code}
}

\begin{code}
sem : interpret-syntax
semClockContext sem = tag
semType sem = Ty
semContext sem = Ctx
semSubst sem = sem-subst
semTerm sem = Tm
_sem∼_ sem = def-eq _ _
_sem≈_ sem = subst-eq _ _
⟦ sem ⟧CCtx = ⟦_⟧Δ
⟦ sem ⟧Type = ⟦_⟧A
⟦ sem ⟧Ctx = ⟦_⟧Γ
⟦ sem ⟧Subst = ⟦_⟧sub
⟦ sem ⟧Tm = ⟦_⟧tm
⟦ sem ⟧∼ = ⟦_⟧tm-eq
⟦ sem ⟧≈ = ⟦_⟧sub-eq

sem-consistent-help : ⊤ ⊎ ⊤ → Set
sem-consistent-help (inj₁ x) = ⊤
sem-consistent-help (inj₂ y) = ⊥

sem-consistent : consistent sem
sem-consistent p = subst sem-consistent-help (p ⊤.tt) ⊤.tt
\end{code}

\AgdaHide{
\begin{code}
syntax-consistent : consistent initial-interpretation
syntax-consistent p = sem-consistent (⟦ sem ⟧∼ p)
\end{code}
}
