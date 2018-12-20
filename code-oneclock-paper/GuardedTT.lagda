\AgdaHide{
\begin{code}
module GuardedTT where

open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Prelude
open import Presheaves
open import CloTT
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
    𝟙-η : {Γ : Context ∅} {A : Type ∅} (t : Term Γ 𝟙) → ⟦ t ⟧Tm ∼ ⟦ t ⟧Tm
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

  ⟦_⟧tm : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} → Term Γ A → Tm ⟦ Γ ⟧Γ ⟦ A ⟧A
  ⟦ sub t s ⟧tm = sem-sub _ _ _ ⟦ t ⟧tm ⟦ s ⟧sub
  ⟦ varTm Γ A ⟧tm = var ⟦ Γ ⟧Γ ⟦ A ⟧A
  ⟦ weakenTm Γ A B t ⟧tm = weaken ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ B ⟧A ⟦ t ⟧tm
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

TRUEnotFALSE-help : ⊤ ⊎ ⊤ → Set
TRUEnotFALSE-help (inj₁ x) = ⊤
TRUEnotFALSE-help (inj₂ y) = ⊥

TRUEnotFALSE : def-eq _ _ ⟦ TRUE ⟧tm ⟦ FALSE ⟧tm → ⊥
TRUEnotFALSE p = subst TRUEnotFALSE-help (p ⊤.tt) ⊤.tt

test : {Γ : Context κ} {A B C : Type κ} (g : Term Γ (later (B ⟶ C))) (f : Term Γ (later (A ⟶ B))) (t : Term Γ (later A))
  → def-eq ⟦ Γ ⟧Γ
           ⟦ later C ⟧A
           ⟦ ((next compmap ⊛ g) ⊛ f) ⊛ t ⟧tm
           ⟦ g ⊛ (f ⊛ t) ⟧tm
test g f t i x =
  Σ≡-uip (funext (λ { [ _ ] → funext (λ { [ _ ] → uip })}))
         (funext (λ { [ j ] → refl}))

open PSh

test2 : {Γ : Context κ} {A B : Type κ} (f : Term Γ (later (A ⟶ B))) (t : Term Γ A)
  → def-eq ⟦ Γ ⟧Γ
           ⟦ later B ⟧A
           ⟦ f ⊛ next t ⟧tm
           ⟦ next (lambdaTm (app-map (varTm _ _) (weakenTm _ _ _ t))) ⊛ f ⟧tm
test2 {Γ} f t i γ =
  Σ≡-uip
    (funext (λ { [ _ ] → funext (λ { [ _ ] → uip })}))
    (funext (λ { [ j ] → cong (λ a → proj₁ (proj₁ (proj₁ ⟦ f ⟧tm i γ) [ j ]) j (proj₁ ⟦ t ⟧tm j a)) (sym (MorId ⟦ Γ ⟧Γ))}))

sem : interpret-syntax
semClockContext sem = tag
semType sem = Ty
semContext sem = Ctx
semSubst sem = sem-subst
semTerm sem = Tm
_∼_ sem = def-eq _ _
⟦ sem ⟧CCtx = ⟦_⟧Δ
⟦ sem ⟧Type = ⟦_⟧A
⟦ sem ⟧Ctx = ⟦_⟧Γ
⟦ sem ⟧Subst = ⟦_⟧sub
⟦ sem ⟧Tm = ⟦_⟧tm
λ-β sem t = beta ⟦ t ⟧tm
λ-η sem t = eta ⟦ t ⟧tm
⊠-β₁ sem t₁ t₂ = pr₁-pair _ _ _ ⟦ t₁ ⟧tm ⟦ t₂ ⟧tm
⊠-β₂ sem t₁ t₂ = pr₂-pair _ _ _ ⟦ t₁ ⟧tm ⟦ t₂ ⟧tm
⊠-η sem t = prod-eta _ _ _ ⟦ t ⟧tm
⊞-β₁ sem l r t = sum-rec-inl _ _ _ _ _ _ ⟦ t ⟧tm
⊞-β₂ sem l r t = sum-rec-inr _ _ _ _ _ _ ⟦ t ⟧tm
𝟙-β sem t = Unit-β _ _ ⟦ t ⟧tm
𝟙-η sem t = Unit-η _ ⟦ t ⟧tm
□-β sem {Γ} {A} t = box-beta {⟦ Γ ⟧Γ} {⟦ A ⟧A} ⟦ t ⟧tm
□-η sem {Γ} {A} t = box-eta {⟦ Γ ⟧Γ} {⟦ A ⟧A} ⟦ t ⟧tm
next-id sem {Γ} {A} t = pure-id-fmap ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ t ⟧tm
next-comp sem {Γ} {A} {B} {C} g f t = test g f t
-- pure-comp-fmap ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ B ⟧A ⟦ C ⟧A ⟦ g ⟧tm ⟦ f ⟧tm ⟦ t ⟧tm -- slow to typecheck
next-⊛ sem f t = pure-fmap-pure _ _ _ ⟦ f ⟧tm ⟦ t ⟧tm
next-λ sem f t = test2 f t -- fmap-pure-fun _ _ _ ⟦ f ⟧tm ⟦ t ⟧tm -- slow to typecheck
fix-f sem f = fix-eq _ _ ⟦ f ⟧tm
fix-u sem f u p = fix-un _ _ ⟦ f ⟧tm ⟦ u ⟧tm p
\end{code}
