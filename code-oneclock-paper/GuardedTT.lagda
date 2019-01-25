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

Now let us put everything together and define interpretations of the syntax defined in \Cref{sec:syntax}.
To give an interpretation, one must give a type of types, contexts, terms, substitutions, and functions mapping the syntactic objects to their interpretations.
In addition, definitional equality and equality between terms must be interpreted and for that, we use setoids.
This means that a relation on terms must be given, which includes the relation \D{∼} as define in \Cref{sec:syntax}, and the same must be done for substitutions.
We define this as a record, whose type declaration is given as

\begin{code}
record interpret-syntax {ℓ₁ ℓ₂} : Set (lsuc (ℓ₁ l⊔ ℓ₂)) where
\end{code}

\AgdaHide{
\begin{code}
  field
    semTy : ClockCtx → Set ℓ₁
    semCtx : ClockCtx → Set ℓ₁
    semTm : ∀ {Δ} → semCtx Δ → semTy Δ → Set ℓ₂
    semSub : ∀ {Δ} → semCtx Δ → semCtx Δ → Set ℓ₂
    _[_sem∼_] : ∀ {Δ} {Γ : semCtx Δ} {A : semTy Δ}
      → semTm Γ A → semTm Γ A → Set ℓ₂
    _[_sem≈_] : ∀ {Δ} {Γ₁ Γ₂ : semCtx Δ} → semSub Γ₁ Γ₂ → semSub Γ₁ Γ₂ → Set ℓ₂
    _⟦_⟧Ty : ∀ {Δ} → Ty Δ → semTy Δ
    _⟦_⟧Ctx : ∀ {Δ} → Ctx Δ → semCtx Δ
    _⟦_⟧Tm : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} → Tm Γ A → semTm (_⟦_⟧Ctx Γ) (_⟦_⟧Ty A)
    _⟦_⟧Sub : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} → Sub Γ₁ Γ₂ → semSub (_⟦_⟧Ctx Γ₁) (_⟦_⟧Ctx Γ₂)
    _⟦_⟧∼ : ∀ {Δ} {Γ : Ctx Δ} {A : Ty Δ} {t t' : Tm Γ A}
      → t ∼ t' → _[_sem∼_] (_⟦_⟧Tm t) (_⟦_⟧Tm t')
    _⟦_⟧≈ : ∀ {Δ} {Γ₁ Γ₂ : Ctx Δ} {s s' : Sub Γ₁ Γ₂}
      → s ≈ s' → _[_sem≈_] (_⟦_⟧Sub s) (_⟦_⟧Sub s')
\end{code}
}

If \AB{sem} is an interpretation of the syntax and \AB{t} is a term, then we write \AB{sem} \AFi{⟦} \AB{t} \AFi{⟧} for the interpretation of \AB{f}.
The main example is the syntax itself.
Tys, contexts, substitutions, terms, and so on are interpreted by themselves.

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
semTy initial-interpretation = Ty
semCtx initial-interpretation = Ctx
semSub initial-interpretation = Sub
semTm initial-interpretation = Tm
_[_sem∼_] initial-interpretation = _∼_
_[_sem≈_] initial-interpretation = _≈_
_⟦_⟧Ty initial-interpretation x = x 
_⟦_⟧Ctx initial-interpretation x = x
_⟦_⟧Sub initial-interpretation x = x
_⟦_⟧Tm initial-interpretation x = x
_⟦_⟧∼ initial-interpretation x = x
_⟦_⟧≈ initial-interpretation x = x
\end{code}
}

We can also interpret the syntax using \Cref{sec:presheaf_sem,sec:guarded}.
This gives categorical semantics of the syntax and we define it as follows.

\begin{code}
sem : interpret-syntax
semTy sem = SemTy
semCtx sem = SemCtx
semTm sem = SemTm
\end{code}

\AgdaHide{
\begin{code}
semSub sem = SemSub
_[_sem∼_] sem = def-eq _ _
_[_sem≈_] sem = subst-eq _ _
_⟦_⟧Ty sem = ⟦_⟧A
_⟦_⟧Ctx sem = ⟦_⟧Γ
_⟦_⟧Sub sem = ⟦_⟧sub
_⟦_⟧Tm sem = ⟦_⟧tm
_⟦_⟧∼ sem = ⟦_⟧tm-eq
_⟦_⟧≈ sem = ⟦_⟧sub-eq
\end{code}
}

Using this semantics, we can conclude the syntax is consistent.
Briefly, consistency means that not every defitional equality.


\begin{code}
bool : Ty ∅
bool = 𝟙 ⊞ 𝟙

TRUE : Tm • bool
TRUE = in₁ 𝟙 tt

FALSE : Tm • bool
FALSE = in₂ 𝟙 tt
\end{code}

Now we can state precisely what consistency means.
We say an interpretation is consistent if \AF{TRUE} and \AF{FALSE} do not have the same interpretation.

\begin{code}
consistent : ∀ {ℓ₁ ℓ₂} → interpret-syntax {ℓ₁} {ℓ₂} → Set ℓ₂
consistent sem = sem [ sem ⟦ TRUE ⟧Tm sem∼ sem ⟦ FALSE ⟧Tm ] → ⊥
\end{code}

\AgdaHide{
\begin{code}
sem-consistent-help : ⊤ ⊎ ⊤ → Set
sem-consistent-help (inj₁ x) = ⊤
sem-consistent-help (inj₂ y) = ⊥
\end{code}
}

The categorical semantics gives rises to a consistent interpretation of the syntax.
To show this, we need to prove that \AIC{inj₁} \AIC{tt} and \AIC{inj₂} \AIC{tt} are not equal where \AIC{tt} is the unique constructor of \AD{⊤}.

\begin{code}
sem-consistent : consistent sem
\end{code}

\AgdaHide{
\begin{code}
sem-consistent p = subst sem-consistent-help (p ⊤.tt) ⊤.tt
\end{code}
}

Finally, we can conclude that the initial interpretation and thus the syntax is consistent.
If we would have a definitional equality between \AF{TRUE} and \AF{FALSE}, then we could interpret that equality in \AF{sem}.
Since the latter leads to a contradiction, the former does too.

\begin{code}
syntax-consistent : consistent initial-interpretation
syntax-consistent p = sem-consistent (sem ⟦ p ⟧∼)
\end{code}

\AgdaHide{
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
