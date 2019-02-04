\AgdaHide{
\begin{code}
module GuardedTT where

open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Level --renaming (suc to lsuc;_⊔_ to _l⊔_)
open import Prelude
open import Prelude.Syntax
open import Presheaves
open import CloTT
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

%If \AB{sem} is an interpretation of the syntax and \AB{t} is a term, then we write \AB{sem} \AFi{⟦} \AB{t} \AFi{⟧} for the interpretation of \AB{t}.
\remove{
The primary example is the syntax itself.
Types, contexts, substitutions, terms, and so on are interpreted by themselves.
This gives rise to the initial interpretation.
}
\AgdaHide{
\begin{code}
open interpret-syntax

-- initial-interpretation : interpret-syntax
-- semTy initial-interpretation = Ty
-- semCtx initial-interpretation = Ctx
-- semSub initial-interpretation = Sub
-- semTm initial-interpretation = Tm
-- _[_sem∼_] initial-interpretation = _∼_
-- _[_sem≈_] initial-interpretation = _≈_
-- _⟦_⟧Ty initial-interpretation x = x 
-- _⟦_⟧Ctx initial-interpretation x = x
-- _⟦_⟧Sub initial-interpretation x = x
-- _⟦_⟧Tm initial-interpretation x = x
-- _⟦_⟧∼ initial-interpretation x = x
-- _⟦_⟧≈ initial-interpretation x = x
\end{code}
}

We also define categorical semantics of the syntax by using the material in \Cref{sec:presheaf_sem,sec:guarded}.
Types and contexts are interpreted as presheaves, and terms are interpreted as natural transformations.
Formally, we define an interpretation \F{sem}.
\AgdaHide{
\begin{code}
mutual
  ⟦_⟧poly' : {Δ : ClockCtx} → Poly Δ → SemPoly Δ
  ⟦_⟧poly' (∁ A) = ∁ ⟦ A ⟧A
  ⟦ I ⟧poly' = I
  ⟦ P ⊞ Q ⟧poly' = ⟦ P ⟧poly' ⊞ ⟦ Q ⟧poly'
  ⟦ P ⊠ Q ⟧poly' = ⟦ P ⟧poly' ⊠ ⟦ Q ⟧poly'
  ⟦ ▻ P ⟧poly' = ▸ ⟦ P ⟧poly'
\end{code}
}
\begin{code}
  ⟦_⟧A' : {Δ : ClockCtx} → Ty Δ → SemTy Δ
  ⟦ 𝟙 ⟧A' = Unit
  ⟦ A ⊞ B ⟧A' = ⟦ A ⟧A' ⊕ ⟦ B ⟧A'
  ⟦ A ⊠ B ⟧A' = ⟦ A ⟧A' ⊗ ⟦ B ⟧A'
  ⟦ A ⟶ B ⟧A' = ⟦ A ⟧A' ⇒ ⟦ B ⟧A'
  ⟦ ⇡ A ⟧A' = ⇑ ⟦ A ⟧A'
  ⟦ ▻ A ⟧A' = ► ⟦ A ⟧A'
  ⟦ □ A ⟧A' = ■ ⟦ A ⟧A'
  ⟦ μ P ⟧A' = mu ⟦ P ⟧poly'  
\end{code}

\begin{code}
sem : interpret-syntax
semTy sem = SemTy
_⟦_⟧Ty sem = ⟦_⟧A
\end{code}

\AgdaHide{
\begin{code}
semCtx sem = SemCtx
semTm sem = SemTm
semSub sem = SemSub
_[_sem∼_] sem = def-eq _ _
_[_sem≈_] sem = subst-eq _ _
_⟦_⟧Ctx sem = ⟦_⟧Γ
_⟦_⟧Sub sem = ⟦_⟧sub
_⟦_⟧Tm sem = ⟦_⟧tm
_⟦_⟧∼ sem = ⟦_⟧tm-eq
_⟦_⟧≈ sem = ⟦_⟧sub-eq
\end{code}
}

Now we show that \GTT\ is consistent, meaning that
not every definitional equality is deducible. 
%that not every definitional equality holds.
We first define a type \F{bool} : \F{Ty} \IC{∅} as \IC{𝟙 ⊞ 𝟙} and two terms \F{TRUE} and \F{FALSE} as \IC{in₁ tt} and \IC{in₂ tt} respectively.
We say that \GTT\ is consistent if \AF{TRUE} and \AF{FALSE} are not definitionally equal.
\AgdaHide{
\begin{code}
bool : Ty ∅
bool = 𝟙 ⊞ 𝟙

TRUE : Tm • bool
TRUE = in₁ 𝟙 tt

FALSE : Tm • bool
FALSE = in₂ 𝟙 tt
\end{code}
}
\begin{code}
consistent : Set
consistent = TRUE ∼ FALSE → ⊥
\end{code}

This is proved by noticing that if \F{TRUE} were definitionally equal to \F{FALSE}, then their interpretations in \AD{sem} would be equal.
However, they are interpreted as \AIC{inj₁} \AIC{tt} and \AIC{inj₂} \AIC{tt} respectively, and those are unequal.
\AgdaHide{
\begin{code}
--consistent : ∀ {ℓ₁ ℓ₂} → interpret-syntax {ℓ₁} {ℓ₂} → Set ℓ₂
--consistent sem = sem [ sem ⟦ TRUE ⟧Tm sem∼ sem ⟦ FALSE ⟧Tm ] → ⊥
sem-consistent-help : ⊤ ⊎ ⊤ → Set
sem-consistent-help (inj₁ x) = ⊤
sem-consistent-help (inj₂ y) = ⊥
\end{code}

\begin{code}
--sem-consistent : consistent sem
\end{code}

\begin{code}
--sem-consistent p = subst sem-consistent-help (p ⊤.tt) ⊤.tt
\end{code}
}
\remove{
Note that the categorical semantics gives rises to a consistent interpretation of the syntax, because \AIC{inj₁} \AIC{tt} and \AIC{inj₂} \AIC{tt} are unequal where \AIC{tt} is the constructor of \AD{⊤}.
From this, we conclude that the initial interpretation is consistent.
This is because whenever we have a definitional equality between \AF{TRUE} and \AF{FALSE}, we could interpret that equality in \AF{sem}.
Since the latter leads to a contradiction, the former does so too.
All in all, we get
}
\AgdaHide{
\begin{code}
syntax-consistent : consistent
syntax-consistent p with (sem ⟦ p ⟧∼) tt
syntax-consistent p | ()
\end{code}

\begin{code}
sub-π₁ : {Δ : ClockCtx} {Γ₁ Γ₂ : Ctx Δ} {A : Ty Δ} {B : Ty Δ} (t : Tm Γ₁ (A ⊠ B)) (s : Sub Γ₂ Γ₁)
  → sub (π₁ t) s ∼ π₁ (sub t s)
sub-π₁ t s =
  trans∼ (sym∼ (⊠-β₁ (sub (π₁ t) s) (sub (π₂ t) s)))
         (cong-π₁ (trans∼ (sym∼ (sub-[ (π₁ t) & (π₂ t) ] s)) (cong-sub (⊠-η t) refl≈)))

sub-π₂ : {Δ : ClockCtx} {Γ₁ Γ₂ : Ctx Δ} {A : Ty Δ} {B : Ty Δ} (t : Tm Γ₁ (A ⊠ B)) (s : Sub Γ₂ Γ₁)
  → sub (π₂ t) s ∼ π₂ (sub t s)
sub-π₂ t s =
  trans∼ (sym∼ (⊠-β₂ (sub (π₁ t) s) (sub (π₂ t) s)))
         (cong-π₂ (trans∼ (sym∼ (sub-[ (π₁ t) & (π₂ t) ] s)) (cong-sub (⊠-η t) refl≈)))

sub-app : {Δ : ClockCtx} {Γ₁ Γ₂ : Ctx Δ} {A : Ty Δ} {B : Ty Δ} (t : Tm Γ₁ (A ⟶ B)) (s : Sub Γ₂ Γ₁)
  → sub (app t) (upA A s) ∼ app (sub t s)
sub-app t s =
  trans∼ (sym∼ (λ-β _))
         (trans∼ (cong-app (sym∼ (sub-lambda (app t) s)))
                 (cong-app (cong-sub (λ-η t) refl≈)))

sub-unbox : {Γ₁ Γ₂ : Ctx ∅} {A : Ty κ} (t : Tm Γ₁ (□ A)) (s : Sub Γ₂ Γ₁)
  → sub (unbox t) (up s) ∼ unbox (sub t s)
sub-unbox t s =
  trans∼ (sym∼ (□-β (sub (unbox t) (up s))))
         (cong-unbox (trans∼ (sym∼ (sub-box (unbox t) s)) (cong-sub (□-η t) refl≈)))

sub-down : {Γ₁ Γ₂ : Ctx ∅} {A : Ty ∅} (t : Tm (⇡ Γ₁) (⇡ A)) (s : Sub Γ₂ Γ₁)
  → sub (down t) s ∼ down(sub t (up s))
sub-down t s =
  trans∼ (sym∼ (up-β (sub (down t) s)))
         (cong-down (trans∼ (sym∼ (sub-up (down t) s)) (cong-sub (up-η t) refl≈)))

sub-tt : {Γ₁ Γ₂ : Ctx ∅} (s : Sub Γ₂ Γ₁) → sub tt s ∼ tt
sub-tt s = 𝟙-η (sub tt s)
\end{code}
}
