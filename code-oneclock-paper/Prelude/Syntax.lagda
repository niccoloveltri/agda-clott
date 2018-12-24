\AgdaHide{
\begin{code}
module Prelude.Syntax where

open import Level
open import Function
open import Data.Empty
\end{code}
}

\begin{code}
data ClockContext : Set where
  ∅ : ClockContext
  κ : ClockContext

mutual
  data Type : ClockContext → Set where
    𝟙        : Type ∅
    _⊞_      : {Δ : ClockContext} → Type Δ → Type Δ → Type Δ
    _⊠_      : {Δ : ClockContext} → Type Δ → Type Δ → Type Δ
    _⟶_    : {Δ : ClockContext} → Type Δ → Type Δ → Type Δ
    weakenT  : Type ∅ → Type κ
    later    : Type κ → Type κ
    clock-q  : Type κ → Type ∅
    μ        : {Δ : ClockContext} → Poly Δ → Type Δ

  data Poly : ClockContext → Set where
    ∁ : {Δ : ClockContext} → Type Δ → Poly Δ
    I : {Δ : ClockContext} → Poly Δ
    _⊞_ : {Δ : ClockContext} → Poly Δ → Poly Δ → Poly Δ
    _⊠_ : {Δ : ClockContext} → Poly Δ → Poly Δ → Poly Δ
    ► : Poly κ → Poly κ

weakenP : Poly ∅ → Poly κ
weakenP (∁ X) = ∁ (weakenT X)
weakenP I = I
weakenP (P ⊞ Q) = weakenP P ⊞ weakenP Q
weakenP (P ⊠ Q) = weakenP P ⊠ weakenP Q

evalP : {Δ : ClockContext} → Poly Δ → Type Δ → Type Δ
evalP (∁ Y) X = Y
evalP I X = X
evalP (P ⊞ Q) X = evalP P X ⊞ evalP Q X
evalP (P ⊠ Q) X = evalP P X ⊠ evalP Q X
evalP (► P) X = later (evalP P X)

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
    weakenS : {Γ Γ' : Context ∅} → Subst Γ Γ' → Subst (weakenC Γ) (weakenC Γ')
    •-to-weaken : Subst • (weakenC •)
    ,-weaken : (Γ : Context ∅) (A : Type ∅) → Subst (weakenC Γ , weakenT A) (weakenC (Γ , A))

  
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
    force     : {Γ : Context ∅} {A : Type κ} → Term Γ (clock-q(later A)) → Term Γ (clock-q A)
    cons      : {Δ : ClockContext} {Γ : Context Δ} (P : Poly Δ) → Term Γ (evalP P (μ P)) → Term Γ (μ P)
    primrec   : {Δ : ClockContext} (P : Poly Δ) {Γ : Context Δ} {A : Type Δ} → Term Γ ((evalP P (μ P) ⊠ evalP P A) ⟶ A) → Term Γ (μ P ⟶ A)
    □const    : {Γ : Context ∅} (A : Type ∅) → Term Γ (clock-q (weakenT A) ⟶ A)
    □sum      : {Γ : Context ∅} (A B : Type κ) → Term Γ (clock-q (A ⊞ B) ⟶ (clock-q A ⊞ clock-q B))
    ⟶weaken : (A B : Type ∅) → Term • (((weakenT A) ⟶ (weakenT B)) ⟶ weakenT(A ⟶ B))
    μweaken   : (P : Poly ∅) → Term • (weakenT (μ P) ⟶ μ (weakenP P))

weaken-to-• : Subst (weakenC •) •
weaken-to-• = ε (weakenC •)

weaken-, : (Γ : Context ∅) (A : Type ∅) → Subst (weakenC (Γ , A)) (weakenC Γ , weakenT A)
weaken-, Γ A = weakenS (pr (idsub (Γ , A))) ,s ⇡ (varTm Γ A)

weakenSA : {Δ : ClockContext} {Γ Γ' : Context Δ} (A : Type Δ) → Subst Γ Γ' → Subst (Γ , A) (Γ' , A)
weakenSA {_} {Γ} {Γ'} A s = (s o pr (idsub (Γ , A))) ,s varTm Γ A

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

⊞map : {Δ : ClockContext} {Γ : Context Δ} {A₁ B₁ A₂ B₂ : Type Δ}
  → Term Γ (A₁ ⟶ A₂) → Term Γ (B₁ ⟶ B₂) → Term Γ ((A₁ ⊞ B₁) ⟶ (A₂ ⊞ B₂))
⊞map {Δ} {Γ} {A₁} {B₁} {A₂} {B₂} f g =
  lambdaTm (⊞rec (A₂ ⊞ B₂)
                 (in₁ B₂ (app-map (weakenTm Γ A₁ (A₁ ⟶ A₂) f) (varTm Γ A₁)))
                 (in₂ A₂ (app-map (weakenTm Γ B₁ (B₁ ⟶ B₂) g) (varTm Γ B₁))))

⊠map : {Δ : ClockContext} {Γ : Context Δ} {A₁ B₁ A₂ B₂ : Type Δ}
  → Term Γ (A₁ ⟶ A₂) → Term Γ (B₁ ⟶ B₂) → Term Γ ((A₁ ⊠ B₁) ⟶ (A₂ ⊠ B₂))
⊠map {Δ} {Γ} {A₁} {B₁} {A₂} {B₂} f g =
  lambdaTm [ app-map (weakenTm Γ (A₁ ⊠ B₁) (A₁ ⟶ A₂) f) (π₁ (varTm Γ (A₁ ⊠ B₁)))
           & app-map (weakenTm Γ (A₁ ⊠ B₁) (B₁ ⟶ B₂) g) (π₂ (varTm Γ (A₁ ⊠ B₁))) ]

►map : {Γ : Context κ} {A B : Type κ}
  → Term Γ (A ⟶ B) → Term Γ (later A ⟶ later B)
►map {Γ} {A} {B} f =
  lambdaTm (weakenTm Γ (later A) (later (A ⟶ B)) (next f) ⊛ varTm Γ (later A))

Pmap : {Δ : ClockContext} (P : Poly Δ) {Γ : Context Δ} {A B : Type Δ}
  → Term Γ (A ⟶ B) → Term Γ (evalP P A ⟶ evalP P B)
Pmap (∁ X) f = idmap X
Pmap I f = f
Pmap (P ⊞ Q) f = ⊞map (Pmap P f) (Pmap Q f)
Pmap (P ⊠ Q) f = ⊠map (Pmap P f) (Pmap Q f)
Pmap (► P) f = ►map (Pmap P f)

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

const□ : (Γ : Context ∅) (A : Type ∅) → Term Γ (A ⟶ clock-q (weakenT A))
const□ Γ A = lambdaTm (box-q (sub (varTm (weakenC Γ) (weakenT A)) (weaken-, Γ A)))

sum□ : {Γ : Context ∅} (A B : Type κ) → Term Γ ((clock-q A ⊞ clock-q B) ⟶ clock-q (A ⊞ B))
sum□ A B = lambdaTm
             (⊞rec (clock-q (A ⊞ B))
                   (□functor (lambdaTm (in₁ B (varTm _ _))) (varTm _ _))
                   (□functor (lambdaTm (in₂ A (varTm _ _))) (varTm _ _)))

□next : {Γ : Context ∅} {A : Type κ} → Term Γ (clock-q A) → Term Γ (clock-q(later A))
□next t = box-q (next (unbox-q t))

⊞weaken : (A B : Type ∅) → Term • (((weakenT A) ⊞ (weakenT B)) ⟶ weakenT(A ⊞ B))
⊞weaken A B = lambdaTm
                (⊞rec (weakenT (A ⊞ B))
                      (sub (⇡ (in₁ B (varTm _ _))) (,-weaken • A o weakenSA (weakenT A) •-to-weaken))
                      (sub (⇡ (in₂ A (varTm _ _))) (,-weaken • B o weakenSA (weakenT B) •-to-weaken)))

help-weaken⊞ : (A B : Type ∅) → Term • ((A ⊞ B) ⟶ clock-q(weakenT A ⊞ weakenT B))
help-weaken⊞ A B = lambdaTm (app-map (sum□ (weakenT A) (weakenT B))
                             (⊞rec (clock-q (weakenT A) ⊞ clock-q (weakenT B))
                                   (in₁ (clock-q (weakenT B)) (box-q (sub (varTm (weakenC •) _) (weaken-, • A))))
                                   (in₂ (clock-q (weakenT A)) (box-q (sub (varTm (weakenC •) _) (weaken-, • B))))))

clock-q-adj₁ : (A : Type ∅) (B : Type κ) → Term • (weakenT A ⟶ B) → Term • (A ⟶ clock-q B)
clock-q-adj₁ A B t = lambdaTm (box-q
                              (app-map
                                (sub (weakenTm (weakenC •) (weakenT A) (weakenT A ⟶ B) (sub t (ε (weakenC •))))
                                     (weaken-, • A))
                                (⇡ (varTm _ _))))

clock-q-adj₂ : (A : Type ∅) (B : Type κ) → Term • (A ⟶ clock-q B) → Term • (weakenT A ⟶ B)
clock-q-adj₂ A B t = lambdaTm (sub (unbox-q (app-map (weakenTm • A (A ⟶ clock-q B) t) (varTm _ _)))
                                   (,-weaken • A o weakenSA (weakenT A) •-to-weaken))

weaken⊞ : (A B : Type ∅) → Term • (weakenT(A ⊞ B) ⟶ ((weakenT A) ⊞ (weakenT B)))
weaken⊞ A B = clock-q-adj₂ (A ⊞ B) (weakenT A ⊞ weakenT B) (help-weaken⊞ A B)

split-prod : {Δ : ClockContext} (Γ : Context Δ) (A B C : Type Δ)
  → Term ((Γ , A) , B) C → Term (Γ , (A ⊠ B)) C
split-prod Γ A B C t = sub t ((pr (idsub (Γ , (A ⊠ B))) ,s π₁ (varTm _ _)) ,s π₂ (varTm _ _))

⊠weaken : (A B : Type ∅) → Term • (((weakenT A) ⊠ (weakenT B)) ⟶ weakenT(A ⊠ B))
⊠weaken A B = lambdaTm (split-prod • (weakenT A) (weakenT B) (weakenT(A ⊠ B))
                                   (sub (⇡ [ weakenTm _ _ _ (varTm _ _) & varTm _ _ ])
                                        (,-weaken (• , A) B o weakenSA (weakenT B) (,-weaken • A o weakenSA (weakenT A) •-to-weaken))))

weaken⊠ : (A B : Type ∅) → Term • (weakenT(A ⊠ B) ⟶ ((weakenT A) ⊠ (weakenT B)))
weaken⊠ A B = lambdaTm [ sub (⇡ (π₁ (varTm • (A ⊠ B)))) (,-weaken • (A ⊠ B) o weakenSA (weakenT (A ⊠ B)) •-to-weaken)
                       & sub (⇡ (π₂ (varTm • (A ⊠ B)))) (,-weaken • (A ⊠ B) o weakenSA (weakenT (A ⊠ B)) •-to-weaken) ]

weaken⟶ : (A B : Type ∅) → Term • (weakenT(A ⟶ B) ⟶ ((weakenT A) ⟶ (weakenT B)))
weaken⟶ A B =
  lambdaTm (lambdaTm
           (sub (⇡ (app-map (weakenTm (• , (A ⟶ B)) A (A ⟶ B) (varTm • (A ⟶ B))) (varTm (• , (A ⟶ B)) A)))
                (,-weaken (• , (A ⟶ B)) A o weakenSA (weakenT A) (,-weaken • (A ⟶ B) o weakenSA (weakenT (A ⟶ B)) •-to-weaken))))
{-
subst-μ-help : {Δ : ClockContext} (Γ : Context Δ) (A B : Type Δ)
  → Subst (Γ , (A ⊠ B)) (Γ , A)
subst-μ-help = {!!}

weaken-evalP : {Γ : Context ∅} (P : Poly ∅) (A : Type ∅)
  → Term (weakenC Γ) (weakenT (evalP P A) ⟶ evalP (weakenP P) (weakenT A))
weaken-evalP {Γ} P A = lambdaTm (sub (varTm (weakenC Γ) _) {!!})

weakenμ : (P : Poly ∅) → Term • (μ (weakenP P) ⟶ weakenT (μ P))
weakenμ P =
  primrec (weakenP P)
          (lambdaTm (sub (⇡ (cons P (varTm • _)))
                         ((,-weaken • (evalP P (μ P)) o
                           (weakenSA (weakenT (evalP P (μ P))) •-to-weaken o
                           {!!})) o
                           subst-μ-help • (evalP (weakenP P) (μ (weakenP P))) (evalP (weakenP P) (weakenT (μ P))))))
-}
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
    cong-force : {Γ : Context ∅} {A : Type κ} {t₁ t₂ : Term Γ (clock-q(later A))} → t₁ ∼ t₂ → force t₁ ∼ force t₂
    cong-cons : {Δ : ClockContext} {Γ : Context Δ} {P : Poly Δ} {t₁ t₂ : Term Γ (evalP P (μ P))} → t₁ ∼ t₂ → cons P t₁ ∼ cons P t₂
    cong-primrec : {Δ : ClockContext} (P : Poly Δ) {Γ : Context Δ} {A : Type Δ} {t₁ t₂ : Term Γ ((evalP P (μ P) ⊠ evalP P A) ⟶ A)}
      → t₁ ∼ t₂ → primrec P t₁ ∼ primrec P t₂
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
    𝟙-η : {Γ : Context ∅} (t : Term Γ 𝟙) → t ∼ tt
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
    primrec-cons : {Δ : ClockContext} (P : Poly Δ) {Γ : Context Δ} {A : Type Δ} (t : Term Γ ((evalP P (μ P) ⊠ evalP P A) ⟶ A)) (a : Term Γ (evalP P (μ P)))
      → app-map (primrec P t) (cons P a) ∼ app-map t [ a & app-map (Pmap P (primrec P t)) a ]
    sub-id : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} (t : Term Γ A)
      → sub t (idsub Γ) ∼ t
    sub-sub : {Δ : ClockContext} {Γ₁ Γ₂ Γ₃ : Context Δ} {A : Type Δ} (t : Term Γ₁ A) (s : Subst Γ₂ Γ₁) (s' : Subst Γ₃ Γ₂)
      → sub (sub t s) s' ∼ sub t (s o s')
    sub-varTm : {Δ : ClockContext} (Γ₁ Γ₂ : Context Δ) (A : Type Δ) (s : Subst Γ₂ Γ₁)
      → sub (varTm Γ₁ A) (weakenSA A s) ∼ varTm Γ₂ A
    sub-unit-rec : {Γ₁ Γ₂ : Context ∅} {A : Type ∅} (t : Term Γ₁ A) (s : Subst Γ₂ Γ₁)
      → sub (unit-rec t) (weakenSA 𝟙 s) ∼ unit-rec (sub t s)
    sub-in₁ : {Δ : ClockContext} {Γ₁ Γ₂ : Context Δ} {A : Type Δ} (B : Type Δ) (t : Term Γ₁ A) (s : Subst Γ₂ Γ₁)
      → sub (in₁ B t) s ∼ in₁ B (sub t s)
    sub-in₂ : {Δ : ClockContext} {Γ₁ Γ₂ : Context Δ} (A : Type Δ) {B : Type Δ} (t : Term Γ₁ B) (s : Subst Γ₂ Γ₁)
      → sub (in₂ B t) s ∼ in₂ B (sub t s)
    sub-[_&_] : {Δ : ClockContext} {Γ₁ Γ₂ : Context Δ} {A : Type Δ} {B : Type Δ} (t₁ : Term Γ₁ A) (t₂ : Term Γ₁ B) (s : Subst Γ₂ Γ₁)
      → sub [ t₁ & t₂ ] s ∼ [ sub t₁ s & sub t₂ s ]
    sub-lambdaTm : {Δ : ClockContext} {Γ₁ Γ₂ : Context Δ} {A : Type Δ} {B : Type Δ} (t : Term (Γ₁ , A) B) (s : Subst Γ₂ Γ₁)
      → sub (lambdaTm t) s ∼ lambdaTm (sub t (weakenSA A s))
    sub-⇡ : {Γ₁ Γ₂ : Context ∅} {A : Type ∅} (t : Term Γ₁ A) (s : Subst Γ₂ Γ₁)
      → sub (⇡ t) (weakenS s) ∼ ⇡(sub t s)
    sub-box-q : {Γ₁ Γ₂ : Context ∅} {A : Type κ} (t : Term (weakenC Γ₁) A) (s : Subst Γ₂ Γ₁)
      → sub (box-q t) s ∼ box-q (sub t (weakenS s))
    sub-next : {Γ₁ Γ₂ : Context κ} {A : Type κ} (t : Term Γ₁ A) (s : Subst Γ₂ Γ₁)
      → sub (next t) s ∼ next (sub t s)
    sub-⊛ : {Γ₁ Γ₂ : Context κ} {A B : Type κ} (f : Term Γ₁ (later (A ⟶ B))) (t : Term Γ₁ (later A)) (s : Subst Γ₂ Γ₁)
      → sub (f ⊛ t) s ∼ (sub f s) ⊛ (sub t s)
    sub-fix-tm : {Γ₁ Γ₂ : Context κ} {A : Type κ} (f : Term Γ₁ (later A ⟶ A)) (s : Subst Γ₂ Γ₁)
      → sub (fix-tm f) s ∼ fix-tm (sub f s)
    sub-force : {Γ₁ Γ₂ : Context ∅} {A : Type κ} (t : Term Γ₁ (clock-q(later A))) (s : Subst Γ₂ Γ₁)
      → sub (force t) s ∼ force (sub t s)
    sub-□const : {Γ₁ Γ₂ : Context ∅} (A : Type ∅) (s : Subst Γ₂ Γ₁)
      → sub (□const A) s ∼ □const A
    sub-□sum : {Γ₁ Γ₂ : Context ∅} (A B : Type κ) (s : Subst Γ₂ Γ₁)
      → sub (□sum A B) s ∼ □sum A B
    sub-cons : {Δ : ClockContext} {Γ₁ Γ₂ : Context Δ} {P : Poly Δ} (t : Term Γ₁ (evalP P (μ P))) (s : Subst Γ₂ Γ₁)
      → sub (cons P t) s ∼ cons P (sub t s)
    sub-primrec : {Δ : ClockContext} (P : Poly Δ) {Γ₁ Γ₂ : Context Δ} {A : Type Δ} (t : Term Γ₁ ((evalP P (μ P) ⊠ evalP P A) ⟶ A)) (s : Subst Γ₂ Γ₁)
      → sub (primrec P t) s ∼ primrec P (sub t s)
    const□const : {Γ : Context ∅} {A : Type ∅} (t : Term Γ (clock-q (weakenT A)))
      → app-map (const□ Γ A) (app-map (□const A) t) ∼ t
    □const□ : {Γ : Context ∅} {A : Type ∅} (t : Term Γ A)
      → app-map (□const A) (app-map (const□ Γ A) t) ∼ t
    □sum□ : {Γ : Context ∅} (A B : Type κ) (t : Term Γ (clock-q A ⊞ clock-q B))
      → app-map (□sum A B) (app-map (sum□ A B) t) ∼ t
    sum□sum : {Γ : Context ∅} (A B : Type κ) (t : Term Γ (clock-q (A ⊞ B)))
      → app-map (sum□ A B) (app-map (□sum A B) t) ∼ t
    force-□next : {Γ : Context ∅} {A : Type κ} (t : Term Γ (clock-q A))
      → force(□next t) ∼ t
    □next-force : {Γ : Context ∅} {A : Type κ} (t : Term Γ (clock-q (later A)))
      → □next(force t) ∼ t
    ⟶weaken⟶ : (A B : Type ∅) (t : Term • (weakenT (A ⟶ B)))
      → app-map (⟶weaken A B) (app-map (weaken⟶ A B) t) ∼ t
    weaken⟶weaken : (A B : Type ∅) (t : Term • (weakenT A ⟶ weakenT B))
      → app-map (weaken⟶ A B) (app-map (⟶weaken A B) t) ∼ t

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
    weaken-ε : (Γ : Context ∅) → weakenS (ε Γ) ≈ (•-to-weaken o ε (weakenC Γ))
    weaken-o : {Γ Γ' Γ'' : Context ∅} (s₁ : Subst Γ' Γ'') (s₂ : Subst Γ Γ') → weakenS (s₁ o s₂) ≈ (weakenS s₁ o weakenS s₂)
    weaken-pr : {Γ Γ' : Context ∅} {A : Type ∅} (s : Subst Γ (Γ' , A)) → weakenS (pr s) ≈ pr (weaken-, Γ' A o weakenS s)
    weaken-idsub : (Γ : Context ∅) → weakenS (idsub Γ) ≈ idsub (weakenC Γ)
    weaken-,s : {Γ Γ' : Context ∅} {A : Type ∅} (s : Subst Γ Γ') (t : Term Γ A) → weakenS (s ,s t) ≈ weakenS (s ,s t)
    weaken-•-id : •-to-weaken o weaken-to-• ≈ idsub (weakenC •)
    •-weaken-id : weaken-to-• o •-to-weaken ≈ idsub •
    weaken-,-id : (Γ : Context ∅) (A : Type ∅) → weaken-, Γ A o ,-weaken Γ A ≈ idsub (weakenC Γ , weakenT A)
    ,-weaken-id : (Γ : Context ∅) (A : Type ∅) → weaken-, Γ A o ,-weaken Γ A ≈ idsub (weakenC Γ , weakenT A)

record interpret-syntax {ℓCC}{ℓTy}{ℓCtx}{ℓSub}{ℓTm}{ℓ∼}{ℓ≈} : Set (suc (ℓCC ⊔ ℓTy ⊔ ℓCtx ⊔ ℓSub ⊔ ℓTm ⊔ ℓ∼ ⊔ ℓ≈)) where
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
