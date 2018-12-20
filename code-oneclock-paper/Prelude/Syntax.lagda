\AgdaHide{
\begin{code}
module Prelude.Syntax where

open import Data.Empty
\end{code}
}

\begin{code}
data ClockContext : Set where
  ∅ : ClockContext
  κ : ClockContext

data Type : ClockContext → Set where
  𝟙        : Type ∅
  _⊞_      : {Δ : ClockContext} → Type Δ → Type Δ → Type Δ
  _⊠_      : {Δ : ClockContext} → Type Δ → Type Δ → Type Δ
  _⟶_    : {Δ : ClockContext} → Type Δ → Type Δ → Type Δ
  weakenT  : Type ∅ → Type κ
  later    : Type κ → Type κ
  clock-q  : Type κ → Type ∅

data Context : ClockContext → Set where
  •          : {Δ : ClockContext} → Context Δ
  _,_        : {Δ : ClockContext} → Context Δ → Type Δ → Context Δ
  weakenC    : Context ∅ → Context κ

mutual
  data Subst : {Δ : ClockContext} → Context Δ → Context Δ → Set where
    ε : {Δ : ClockContext} (Γ : Context Δ) → Subst Γ •
    idsub : {Δ : ClockContext} (Γ : Context Δ) → Subst Γ Γ
    _,s_ : {Δ : ClockContext} {Γ Γ' : Context Δ} {A : Type Δ} → Subst Γ Γ' → Term Γ A → Subst Γ (Γ' , A)
    _o_ : {Δ : ClockContext} {Γ Γ' Γ'' : Context Δ} → Subst Γ' Γ'' → Subst Γ Γ' → Subst Γ Γ''
    pr : {Δ : ClockContext} {Γ Γ' : Context Δ} {A : Type Δ} → Subst Γ (Γ' , A) → Subst Γ Γ'
  
  data Term   : {Δ : ClockContext} → Context Δ → Type Δ → Set where
    sub       : {Δ : ClockContext} {Γ Γ' : Context Δ} {A : Type Δ} → Term Γ' A → Subst Γ Γ' → Term Γ A
    varTm    : {Δ : ClockContext} (Γ : Context Δ) (A : Type Δ) → Term (Γ , A) A
    weakenTm  : {Δ : ClockContext} (Γ : Context Δ) (A B : Type Δ) → Term Γ B → Term (Γ , A) B
    tt        : {Γ : Context ∅} → Term Γ 𝟙
    unit-rec  : {Γ : Context ∅} {A : Type ∅} → Term Γ A → Term (Γ , 𝟙) A
    in₁       : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} (B : Type Δ) → Term Γ A → Term Γ (A ⊞ B)
    in₂       : {Δ : ClockContext} {Γ : Context Δ} (A : Type Δ) {B : Type Δ} → Term Γ B → Term Γ (A ⊞ B)
    ⊞rec      : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (C : Type Δ) → Term (Γ , A) C → Term (Γ , B) C → Term (Γ , (A ⊞ B)) C
    [_&_]     : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} → Term Γ A → Term Γ B → Term Γ (A ⊠ B)
    π₁       : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} → Term Γ (A ⊠ B) → Term Γ A
    π₂       : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} → Term Γ (A ⊠ B) → Term Γ B
    lambdaTm  : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} → Term (Γ , A) B → Term Γ (A ⟶ B)
    appTm     : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} → Term Γ (A ⟶ B) → Term (Γ , A) B
    ⇡         : {Γ : Context ∅} {A : Type ∅} → Term Γ A → Term (weakenC Γ) (weakenT A)
    ↓         : {Γ : Context ∅} {A : Type ∅} → Term (weakenC Γ) (weakenT A) → Term Γ A
    box-q     : {Γ : Context ∅} {A : Type κ} → Term (weakenC Γ) A → Term Γ (clock-q A)
    unbox-q   : {Γ : Context ∅} {A : Type κ} → Term Γ (clock-q A) → Term (weakenC Γ) A
    next      : {Γ : Context κ} {A : Type κ} → Term Γ A → Term Γ (later A)
    _⊛_       : {Γ : Context κ} {A B : Type κ} → Term Γ (later (A ⟶ B)) → Term Γ (later A) → Term Γ (later B)
    fix-tm    : {Γ : Context κ} {A : Type κ} → Term Γ (later A ⟶ A) → Term Γ A
    force     : {Γ : Context ∅} {A : Type κ} → Term Γ (clock-q(later A)) → Term Γ (clock-q A)
    □const    : {Γ : Context ∅} (A : Type ∅) → Term Γ (clock-q (weakenT A) ⟶ A)
    □sum      : {Γ : Context ∅} (A B : Type κ) → Term Γ (clock-q (A ⊞ B) ⟶ (clock-q A ⊞ clock-q B))

bool : Type ∅
bool = 𝟙 ⊞ 𝟙

TRUE : Term • bool
TRUE = in₁ 𝟙 tt

FALSE : Term • bool
FALSE = in₂ 𝟙 tt

app-map : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} → Term Γ (A ⟶ B) → Term Γ A → Term Γ B
app-map {_} {Γ} {A} {B} f x = sub (appTm f) (idsub Γ ,s x)

idmap : {Δ : ClockContext} {Γ : Context Δ} (A : Type Δ) → Term Γ (A ⟶ A)
idmap {_} {Γ} A = lambdaTm (varTm Γ A)

compmap : {Δ : ClockContext} {Γ : Context Δ} {A B C : Type Δ} → Term Γ ((B ⟶ C) ⟶ ((A ⟶ B) ⟶ (A ⟶ C)))
compmap {_} {Γ} {A} {B} {C} =
  lambdaTm
    (lambdaTm
      (lambdaTm
        (app-map
          (weakenTm _ _ _ (weakenTm _ _ _ (varTm _ _)))
          (app-map
            (weakenTm _ _ _ (varTm _ _))
            (varTm _ _)))))

□functor : {Γ : Context ∅} {A B : Type κ} → Term (weakenC Γ) (A ⟶ B) → Term Γ (clock-q A) → Term Γ (clock-q B)
□functor f t = box-q (app-map f (unbox-q t))

record interpret-syntax : Set₂ where
  field
    semClockContext : Set
    semType : semClockContext → Set₁
    semContext : semClockContext → Set₁
    semSubst : {Δ : semClockContext} → semContext Δ → semContext Δ → Set
    semTerm : {Δ : semClockContext} → semContext Δ → semType Δ → Set
    _∼_ : {Δ : semClockContext} {Γ : semContext Δ} {A : semType Δ} → semTerm Γ A → semTerm Γ A → Set -- \sim
    ⟦_⟧CCtx : ClockContext → semClockContext
    ⟦_⟧Type : {Δ : ClockContext} → Type Δ → semType ⟦ Δ ⟧CCtx
    ⟦_⟧Ctx : {Δ : ClockContext} → Context Δ → semContext ⟦ Δ ⟧CCtx
    ⟦_⟧Subst : {Δ : ClockContext} {Γ Γ' : Context Δ} → Subst Γ Γ' → semSubst ⟦ Γ ⟧Ctx ⟦ Γ' ⟧Ctx
    ⟦_⟧Tm : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} → Term Γ A → semTerm ⟦ Γ ⟧Ctx ⟦ A ⟧Type
    λ-β : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t : Term (Γ , A) B) → ⟦ appTm (lambdaTm t) ⟧Tm ∼ ⟦ t ⟧Tm
    λ-η : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t : Term Γ (A ⟶ B)) → ⟦ lambdaTm (appTm t) ⟧Tm ∼ ⟦ t ⟧Tm
    ⊠-β₁ : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t₁ : Term Γ A) (t₂ : Term Γ B) → ⟦ π₁ [ t₁ & t₂ ] ⟧Tm ∼ ⟦ t₁ ⟧Tm
    ⊠-β₂ : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t₁ : Term Γ A) (t₂ : Term Γ B) → ⟦ π₂ [ t₁ & t₂ ] ⟧Tm ∼ ⟦ t₂ ⟧Tm
    ⊠-η : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t : Term Γ (A ⊠ B)) → ⟦ [ π₁ t & π₂ t ] ⟧Tm ∼ ⟦ t ⟧Tm
    ⊞-β₁ : {Δ : ClockContext} {Γ : Context Δ} {A B C : Type Δ} (l : Term (Γ , A) C) (r : Term (Γ , B) C) (t : Term Γ A)
        → ⟦ sub (⊞rec C l r) (idsub Γ ,s in₁ B t) ⟧Tm ∼ ⟦ sub l (idsub Γ ,s t) ⟧Tm
    ⊞-β₂ : {Δ : ClockContext} {Γ : Context Δ} {A B C : Type Δ} (l : Term (Γ , A) C) (r : Term (Γ , B) C) (t : Term Γ B)
        → ⟦ sub (⊞rec C l r) (idsub Γ ,s in₂ A t) ⟧Tm ∼ ⟦ sub r (idsub Γ ,s t) ⟧Tm
    𝟙-β : {Γ : Context ∅} {A : Type ∅} (t : Term Γ A) → ⟦ sub (unit-rec t) (idsub Γ ,s tt) ⟧Tm ∼ ⟦ t ⟧Tm
    𝟙-η : {Γ : Context ∅} {A : Type ∅} (t : Term Γ 𝟙) → ⟦ t ⟧Tm ∼ ⟦ tt ⟧Tm
    □-β : {Γ : Context ∅} {A : Type κ} (t : Term (weakenC Γ) A) → ⟦ unbox-q (box-q t) ⟧Tm ∼ ⟦ t ⟧Tm
    □-η : {Γ : Context ∅} {A : Type κ} (t : Term Γ (clock-q A)) → ⟦ box-q (unbox-q t) ⟧Tm ∼ ⟦ t ⟧Tm
    next-id : {Γ : Context κ} {A : Type κ} (t : Term Γ (later A)) → ⟦ next (idmap A) ⊛ t ⟧Tm ∼ ⟦ t ⟧Tm
    next-comp : {Γ : Context κ} {A B C : Type κ} (g : Term Γ (later (B ⟶ C))) (f : Term Γ (later (A ⟶ B))) (t : Term Γ (later A))
      → ⟦ ((next compmap ⊛ g) ⊛ f) ⊛ t  ⟧Tm ∼ ⟦ g ⊛ (f ⊛ t) ⟧Tm
    next-⊛ : {Γ : Context κ} {A B : Type κ} (f : Term Γ (A ⟶ B)) (t : Term Γ A) → ⟦ next f ⊛ next t ⟧Tm ∼ ⟦ next (app-map f t) ⟧Tm
    next-λ : {Γ : Context κ} {A B : Type κ} (f : Term Γ (later (A ⟶ B))) (t : Term Γ A)
      → ⟦ f ⊛ next t ⟧Tm ∼ ⟦ next (lambdaTm (app-map (varTm _ _) (weakenTm _ _ _ t))) ⊛ f ⟧Tm
    fix-f : {Γ : Context κ} {A : Type κ} (f : Term Γ (later A ⟶ A)) → ⟦ fix-tm f ⟧Tm ∼ ⟦ app-map f (next (fix-tm f)) ⟧Tm
    fix-u : {Γ : Context κ} {A : Type κ} (f : Term Γ (later A ⟶ A)) (u : Term Γ A) → ⟦ app-map f (next u) ⟧Tm ∼ ⟦ u ⟧Tm → ⟦ fix-tm f ⟧Tm ∼ ⟦ u ⟧Tm
open interpret-syntax

consistent : interpret-syntax → Set
consistent sem = (_∼_ sem (⟦ sem ⟧Tm TRUE) (⟦ sem ⟧Tm FALSE)) → ⊥
\end{code}
