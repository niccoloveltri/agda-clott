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
--    force     : {Γ : Context ∅} {A : Type κ} → Term Γ (clock-q(later A)) → Term Γ (clock-q A)
--    □const    : {Γ : Context ∅} (A : Type ∅) → Term Γ (clock-q (weakenT A) ⟶ A)
--    □sum      : {Γ : Context ∅} (A B : Type κ) → Term Γ (clock-q (A ⊞ B) ⟶ (clock-q A ⊞ clock-q B))


bool : Type ∅
bool = 𝟙 ⊞ 𝟙

TRUE : Term • bool
TRUE = in₁ 𝟙 tt

FALSE : Term • bool
FALSE = in₂ 𝟙 tt

weakenTm  : {Δ : ClockContext} (Γ : Context Δ) (A B : Type Δ) → Term Γ B → Term (Γ , A) B
weakenTm Γ A B x = sub x (pr (idsub (Γ , A)))

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

infix 13 _∼_ _≈_

mutual
  data _∼_ : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} → Term Γ A → Term Γ A → Set where -- \sim
    refl∼ : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {t : Term Γ A} → t ∼ t
    sym∼ : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {t₁ t₂ : Term Γ A} → t₁ ∼ t₂ → t₂ ∼ t₁
    trans∼ : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {t₁ t₂ t₃ : Term Γ A} → t₁ ∼ t₂ → t₂ ∼ t₃ → t₁ ∼ t₃
    cong-sub : {Δ : ClockContext} {Γ Γ' : Context Δ} {A : Type Δ} {t₁ t₂ : Term Γ' A} {s₁ s₂ : Subst Γ Γ'} → t₁ ∼ t₂ → s₁ ≈ s₂ → sub t₁ s₁ ∼ sub t₂ s₂
    cong-unit-rec  : {Γ : Context ∅} {A : Type ∅} {t₁ t₂ : Term Γ A} → t₁ ∼ t₂ → unit-rec t₁ ∼ unit-rec t₂
    cong-in₁ : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} (B : Type Δ) {t₁ t₂ : Term Γ A} → t₁ ∼ t₂ → in₁ A t₁ ∼ in₁ A t₂
    cong-in₂ : {Δ : ClockContext} {Γ : Context Δ} (A : Type Δ) {B : Type Δ} {t₁ t₂ : Term Γ B} → t₁ ∼ t₂ → in₂ B t₁ ∼ in₂ B t₂
    cong-⊞rec : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (C : Type Δ) {t₁ t₂ : Term (Γ , A) C} {u₁ u₂ : Term (Γ , B) C}
      → t₁ ∼ t₂ → u₁ ∼ u₂ → ⊞rec C t₁ u₁ ∼ ⊞rec C t₂ u₂
    cong-[_&_] : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} {t₁ t₂ : Term Γ A} {u₁ u₂ : Term Γ B}
      → t₁ ∼ t₂ → u₁ ∼ u₂ → [ t₁ & u₁ ] ∼ [ t₂ & u₂ ]
    cong-π₁ : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} {t₁ t₂ : Term Γ (A ⊠ B)} → t₁ ∼ t₂ → π₁ t₁ ∼ π₁ t₂
    cong-π₂ : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} {t₁ t₂ : Term Γ (A ⊠ B)} → t₁ ∼ t₂ → π₂ t₁ ∼ π₂ t₂
    cong-lambdaTm : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} {t₁ t₂ : Term (Γ , A) B} → t₁ ∼ t₂ → lambdaTm t₁ ∼ lambdaTm t₂
    cong-appTm  : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} {t₁ t₂ : Term Γ (A ⟶ B)} → t₁ ∼ t₂ → appTm t₁ ∼ appTm t₂
    cong-⇡ : {Γ : Context ∅} {A : Type ∅} {t₁ t₂ : Term Γ A} → t₁ ∼ t₂ → ⇡ t₁ ∼ ⇡ t₂
    cong-↓ : {Γ : Context ∅} {A : Type ∅} {t₁ t₂ : Term (weakenC Γ) (weakenT A)} → t₁ ∼ t₂ → ↓ t₁ ∼ ↓ t₂
    cong-box-q : {Γ : Context ∅} {A : Type κ} {t₁ t₂ : Term (weakenC Γ) A} → t₁ ∼ t₂ → box-q t₁ ∼ box-q t₂
    cong-unbox-q : {Γ : Context ∅} {A : Type κ} {t₁ t₂ : Term Γ (clock-q A)} → t₁ ∼ t₂ → unbox-q t₁ ∼ unbox-q t₂
    cong-next : {Γ : Context κ} {A : Type κ} {t₁ t₂ : Term Γ A} → t₁ ∼ t₂ → next t₁ ∼ next t₂
    cong-_⊛_ : {Γ : Context κ} {A B : Type κ} {t₁ t₂ : Term Γ (later (A ⟶ B))} {u₁ u₂ : Term Γ (later A)} → t₁ ∼ t₂ → u₁ ∼ u₂ → t₁ ⊛ u₁ ∼ t₂ ⊛ u₂
    cong-fix-tm  : {Γ : Context κ} {A : Type κ} {t₁ t₂ : Term Γ (later A ⟶ A)} → t₁ ∼ t₂ → fix-tm t₁ ∼ fix-tm t₂
    λ-β : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t : Term (Γ , A) B) → appTm (lambdaTm t) ∼ t
    λ-η : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t : Term Γ (A ⟶ B)) → lambdaTm (appTm t) ∼ t
    ⊠-β₁ : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t₁ : Term Γ A) (t₂ : Term Γ B) → π₁ [ t₁ & t₂ ] ∼ t₁
    ⊠-β₂ : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t₁ : Term Γ A) (t₂ : Term Γ B) → π₂ [ t₁ & t₂ ] ∼ t₂
    ⊠-η : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t : Term Γ (A ⊠ B)) → [ π₁ t & π₂ t ] ∼ t
    ⊞-β₁ : {Δ : ClockContext} {Γ : Context Δ} {A B C : Type Δ} (l : Term (Γ , A) C) (r : Term (Γ , B) C) (t : Term Γ A)
        → sub (⊞rec C l r) (idsub Γ ,s in₁ B t) ∼ sub l (idsub Γ ,s t)
    ⊞-β₂ : {Δ : ClockContext} {Γ : Context Δ} {A B C : Type Δ} (l : Term (Γ , A) C) (r : Term (Γ , B) C) (t : Term Γ B)
        → sub (⊞rec C l r) (idsub Γ ,s in₂ A t) ∼ sub r (idsub Γ ,s t)
    𝟙-β : {Γ : Context ∅} {A : Type ∅} (t : Term Γ A) → sub (unit-rec t) (idsub Γ ,s tt) ∼ t
    𝟙-η : {Γ : Context ∅} {A : Type ∅} (t : Term Γ 𝟙) → t ∼ tt
    □-β : {Γ : Context ∅} {A : Type κ} (t : Term (weakenC Γ) A) → unbox-q (box-q t) ∼ t
    □-η : {Γ : Context ∅} {A : Type κ} (t : Term Γ (clock-q A)) → box-q (unbox-q t) ∼ t
    ⇡-β : {Γ : Context ∅} {A : Type ∅} (t : Term Γ A) → ↓ (⇡ t) ∼ t
    ⇡-η : {Γ : Context ∅} {A : Type ∅} (t : Term (weakenC Γ) (weakenT A)) → ⇡ (↓ t) ∼ t
    next-id : {Γ : Context κ} {A : Type κ} (t : Term Γ (later A)) → next (idmap A) ⊛ t ∼ t
    next-comp : {Γ : Context κ} {A B C : Type κ} (g : Term Γ (later (B ⟶ C))) (f : Term Γ (later (A ⟶ B))) (t : Term Γ (later A))
      → ((next compmap ⊛ g) ⊛ f) ⊛ t ∼ g ⊛ (f ⊛ t)
    next-⊛ : {Γ : Context κ} {A B : Type κ} (f : Term Γ (A ⟶ B)) (t : Term Γ A) → next f ⊛ next t ∼ next (app-map f t)
    next-λ : {Γ : Context κ} {A B : Type κ} (f : Term Γ (later (A ⟶ B))) (t : Term Γ A)
      → f ⊛ next t ∼ next (lambdaTm (app-map (varTm _ _) (weakenTm _ _ _ t))) ⊛ f
    fix-f : {Γ : Context κ} {A : Type κ} (f : Term Γ (later A ⟶ A)) → fix-tm f ∼ app-map f (next (fix-tm f))
    fix-u : {Γ : Context κ} {A : Type κ} (f : Term Γ (later A ⟶ A)) (u : Term Γ A) → app-map f (next u) ∼ u → fix-tm f ∼ u

  data _≈_ : {Δ : ClockContext} {Γ Γ' : Context Δ} → Subst Γ Γ' → Subst Γ Γ' → Set where -- ≈
    refl≈ : {Δ : ClockContext} {Γ Γ' : Context Δ} {s : Subst Γ Γ'} → s ≈ s
    sym≈ : {Δ : ClockContext} {Γ Γ' : Context Δ} {s₁ s₂ : Subst Γ Γ'} → s₁ ≈ s₂ → s₂ ≈ s₁
    trans≈ : {Δ : ClockContext} {Γ Γ' : Context Δ} {s₁ s₂ s₃ : Subst Γ Γ'} → s₁ ≈ s₂ → s₂ ≈ s₃ → s₁ ≈ s₃
    cong-_,s_ : {Δ : ClockContext} {Γ Γ' : Context Δ} {A : Type Δ} {s₁ s₂ : Subst Γ Γ'} {t₁ t₂ : Term Γ A} → s₁ ≈ s₂ → t₁ ∼ t₂ → s₁ ,s t₁ ≈ s₂ ,s t₂
    cong-_o_ : {Δ : ClockContext} {Γ Γ' Γ'' : Context Δ} {s₁ s₂ : Subst Γ' Γ''} {σ₁ σ₂ : Subst Γ Γ'} → s₁ ≈ s₂ → σ₁ ≈ σ₂ → s₁ o σ₁ ≈ s₂ o σ₂
    cong-pr : {Δ : ClockContext} {Γ Γ' : Context Δ} {A : Type Δ} {s₁ s₂ : Subst Γ (Γ' , A)} → s₁ ≈ s₂ → pr s₁ ≈ pr s₂
    sub-idl : {Δ : ClockContext} {Γ Γ' : Context Δ} (s : Subst Γ Γ') → idsub Γ' o s ≈ s
    sub-idr : {Δ : ClockContext} {Γ Γ' : Context Δ} (s : Subst Γ Γ') → s o idsub Γ ≈ s
    sub-assoc : {Δ : ClockContext} {Γ₁ Γ₂ Γ₃ Γ₄ : Context Δ} (s₁ : Subst Γ₁ Γ₂) (s₂ : Subst Γ₂ Γ₃) (s₃ : Subst Γ₃ Γ₄)
      → s₃ o (s₂ o s₁) ≈ (s₃ o s₂) o s₁
    sub-π₁β : {Δ : ClockContext} {Γ Γ' : Context Δ} {A : Type Δ} {t : Term Γ A} (s : Subst Γ Γ')
      → pr (s ,s t) ≈ s
    sub-εη : {Δ : ClockContext} {Γ : Context Δ} (s : Subst Γ •) → s ≈ ε Γ
    sub-,o : {Δ : ClockContext} {Γ₁ Γ₂ Γ₃ : Context Δ} {A : Type Δ} {t : Term Γ₂ A} (s₁ : Subst Γ₁ Γ₂) (s₂ : Subst Γ₂ Γ₃)
      → (s₂ ,s t) o s₁ ≈ (s₂ o s₁) ,s sub t s₁
    sub-η : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} (s : Subst Γ (Γ , A))
      → pr s ,s sub (varTm Γ A) s ≈ s

record interpret-syntax : Set₂ where
  field
    semClockContext : Set
    semType : semClockContext → Set₁
    semContext : semClockContext → Set₁
    semSubst : {Δ : semClockContext} → semContext Δ → semContext Δ → Set
    semTerm : {Δ : semClockContext} → semContext Δ → semType Δ → Set
    _sem∼_ : {Δ : semClockContext} {Γ : semContext Δ} {A : semType Δ} → semTerm Γ A → semTerm Γ A → Set -- \sim
    _sem≈_ : {Δ : semClockContext} {Γ Γ' : semContext Δ} → semSubst Γ Γ' → semSubst Γ Γ' → Set -- ≈
    ⟦_⟧CCtx : ClockContext → semClockContext
    ⟦_⟧Type : {Δ : ClockContext} → Type Δ → semType ⟦ Δ ⟧CCtx
    ⟦_⟧Ctx : {Δ : ClockContext} → Context Δ → semContext ⟦ Δ ⟧CCtx
    ⟦_⟧Subst : {Δ : ClockContext} {Γ Γ' : Context Δ} → Subst Γ Γ' → semSubst ⟦ Γ ⟧Ctx ⟦ Γ' ⟧Ctx
    ⟦_⟧Tm : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} → Term Γ A → semTerm ⟦ Γ ⟧Ctx ⟦ A ⟧Type
    ⟦_⟧∼ : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {t t' : Term Γ A} → t ∼ t' → ⟦ t ⟧Tm sem∼ ⟦ t' ⟧Tm
    ⟦_⟧≈ : {Δ : ClockContext} {Γ Γ' : Context Δ} {s s' : Subst Γ Γ'} → s ≈ s' → ⟦ s ⟧Subst sem≈ ⟦ s' ⟧Subst

open interpret-syntax

consistent : interpret-syntax → Set
consistent sem = (_sem∼_ sem (⟦ sem ⟧Tm TRUE) (⟦ sem ⟧Tm FALSE)) → ⊥

{-
record interpret-syntax : Set₂ where
  field
    semClockContext : Set
    semType : semClockContext → Set₁
    semContext : semClockContext → Set₁
    semSubst : {Δ : semClockContext} → semContext Δ → semContext Δ → Set
    semTerm : {Δ : semClockContext} → semContext Δ → semType Δ → Set
    _∼_ : {Δ : semClockContext} {Γ : semContext Δ} {A : semType Δ} → semTerm Γ A → semTerm Γ A → Set -- \sim
    _≈_ : {Δ : semClockContext} {Γ Γ' : semContext Δ} → semSubst Γ Γ' → semSubst Γ Γ' → Set -- ≈
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
    sub-idl : {Δ : ClockContext} {Γ Γ' : Context Δ} (s : Subst Γ Γ') → ⟦ idsub Γ' o s ⟧Subst ≈ ⟦ s ⟧Subst
    sub-idr : {Δ : ClockContext} {Γ Γ' : Context Δ} (s : Subst Γ Γ') → ⟦ s o idsub Γ ⟧Subst ≈ ⟦ s ⟧Subst
    sub-assoc : {Δ : ClockContext} {Γ₁ Γ₂ Γ₃ Γ₄ : Context Δ} (s₁ : Subst Γ₁ Γ₂) (s₂ : Subst Γ₂ Γ₃) (s₃ : Subst Γ₃ Γ₄)
      → ⟦ s₃ o (s₂ o s₁) ⟧Subst ≈ ⟦ (s₃ o s₂) o s₁ ⟧Subst
    sub-π₁β : {Δ : ClockContext} {Γ Γ' : Context Δ} {A : Type Δ} {t : Term Γ A} (s : Subst Γ Γ')
      → ⟦ pr (s ,s t) ⟧Subst ≈ ⟦ s ⟧Subst
    sub-εη : {Δ : ClockContext} {Γ : Context Δ} (s : Subst Γ •) → ⟦ s ⟧Subst ≈ ⟦ ε Γ ⟧Subst
    sub-,o : {Δ : ClockContext} {Γ₁ Γ₂ Γ₃ : Context Δ} {A : Type Δ} {t : Term Γ₂ A} (s₁ : Subst Γ₁ Γ₂) (s₂ : Subst Γ₂ Γ₃)
      → ⟦ (s₂ ,s t) o s₁ ⟧Subst ≈ ⟦ (s₂ o s₁) ,s sub t s₁ ⟧Subst
    sub-η : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} (s : Subst Γ (Γ , A))
      → ⟦ pr s ,s sub (varTm Γ A) s ⟧Subst ≈ ⟦ s ⟧Subst
-}
\end{code}
