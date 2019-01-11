\AgdaHide{
\begin{code}
module Prelude.Syntax where

open import Level
open import Function
open import Data.Empty
\end{code}
}

We now give a description of the object type theory. This is a simple
type theory with guarded recursion that can be seen as a variant of
Atkey and McBride's type system \cite{atkey2013productive} but
allowing the presence of at most one clock in context.
In Atkey and McBride's system, judgements are parametrized by a clock
context. In our case, the clock context can either be empty or contain
a single clock \IC{κ}.

\begin{code}
data ClockContext : Set where
  ∅ : ClockContext
  κ : ClockContext
\end{code}

\AgdaHide{
\begin{code}
mutual
\end{code}
}

Types depend on a clock context. 

\begin{AgdaAlign}
\begin{code}
  data Type : ClockContext → Set where
\end{code}

We have the unit type which exists only in the empty clock context. We
have products, coproducts and function spaces which exist in all clock
contexts.

\begin{code}
    𝟙 : Type ∅
    _⊞_ : ∀ {Δ} → Type Δ → Type Δ → Type Δ
    _⊠_ : ∀ {Δ} → Type Δ → Type Δ → Type Δ
    _⟶_ : ∀ {Δ} → Type Δ → Type Δ → Type Δ
\end{code}

In addition to the usual simple type formers, there are types that
allow us to specify guarded recursive and coinductive types. We have
the later modality, which takes a type in the \IC{κ} clock context and
returns a type in the \IC{κ} clock context.
We have clock quantification, which takes a type in the \IC{κ} clock
context and returns a type in the \IC{∅} clock context. We also have a
weakening type former, which embeds any type in the \IC{∅} clock context
into types in the \IC{κ} clock context.

\begin{code}
    later : Type κ → Type κ
    clock-q : Type κ → Type ∅
    weakenT : Type ∅ → Type κ
\end{code}

Finally we have guarded recursive types which exist in all clock
contexts. 

\begin{code}
    μ : ∀ {Δ} → Poly Δ → Type Δ
\end{code}
\end{AgdaAlign}

A guarded recursive type in a clock context \Ar{Δ} takes an element of
\F{Poly} \Ar{Δ} as its input. We call these elements polynomials. Each
polynomial \Ar{P} corresponds to a functor, and \IC{μ} \Ar{P} is the
least fixed point of \Ar{P}. Typically for this fixpoint to exists one
considers strictly positive functors. Here we consider a restricted
grammar for functors, consisting of constant functors, the identity
functor, products, coproducts, the later modality.
The type family \F{Poly} is defined mutually with \F{Type}.


\begin{code}
  data Poly : ClockContext → Set where
    ∁ : ∀ {Δ} → Type Δ → Poly Δ
    I : ∀ {Δ} → Poly Δ
    _⊞_ : ∀ {Δ} → Poly Δ → Poly Δ → Poly Δ
    _⊠_ : ∀ {Δ} → Poly Δ → Poly Δ → Poly Δ
    ► : Poly κ → Poly κ
\end{code}

\AgdaHide{
\begin{code}
weakenP : Poly ∅ → Poly κ
weakenP (∁ X) = ∁ (weakenT X)
weakenP I = I
weakenP (P ⊞ Q) = weakenP P ⊞ weakenP Q
weakenP (P ⊠ Q) = weakenP P ⊠ weakenP Q
\end{code}
}

\begin{code}
evalP : ∀ {Δ} → Poly Δ → Type Δ → Type Δ
\end{code}

\AgdaHide{
\begin{code}
evalP (∁ Y) X = Y
evalP I X = X
evalP (P ⊞ Q) X = evalP P X ⊞ evalP Q X
evalP (P ⊠ Q) X = evalP P X ⊠ evalP Q X
evalP (► P) X = later (evalP P X)
\end{code}
}

\begin{code}
data Context : ClockContext → Set where
  • : ∀ {Δ} → Context Δ
  _,_ : ∀ {Δ} → Context Δ → Type Δ → Context Δ
  weakenC : Context ∅ → Context κ
\end{code}

\AgdaHide{
\begin{code}
mutual
\end{code}
}
\begin{code}
  data Term : ∀ {Δ} → Context Δ → Type Δ → Set where
    sub : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {A : Type Δ}
      → Term Γ₂ A → Subst Γ₁ Γ₂ → Term Γ₁ A
    varTm : ∀ {Δ} (Γ : Context Δ) (A : Type Δ) → Term (Γ , A) A
    tt : {Γ : Context ∅} → Term Γ 𝟙
    unit-rec : {Γ : Context ∅} {A : Type ∅} → Term Γ A → Term (Γ , 𝟙) A
    in₁ : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} (B : Type Δ) → Term Γ A → Term Γ (A ⊞ B)
    in₂ : ∀ {Δ} {Γ : Context Δ} (A : Type Δ) {B : Type Δ} → Term Γ B → Term Γ (A ⊞ B)
    ⊞rec : ∀ {Δ} {Γ : Context Δ} {A B : Type Δ} (C : Type Δ)
      → Term (Γ , A) C → Term (Γ , B) C → Term (Γ , (A ⊞ B)) C
    [_&_] : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} {B : Type Δ}
      → Term Γ A → Term Γ B → Term Γ (A ⊠ B)
    π₁ : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} → Term Γ (A ⊠ B) → Term Γ A
    π₂ : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} → Term Γ (A ⊠ B) → Term Γ B
    lambdaTm : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} {B : Type Δ}
      → Term (Γ , A) B → Term Γ (A ⟶ B)
    appTm : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} {B : Type Δ}
      → Term Γ (A ⟶ B) → Term (Γ , A) B
    ⇡ : {Γ : Context ∅} {A : Type ∅} → Term Γ A → Term (weakenC Γ) (weakenT A)
    ↓ : {Γ : Context ∅} {A : Type ∅} → Term (weakenC Γ) (weakenT A) → Term Γ A
    box-q : {Γ : Context ∅} {A : Type κ} → Term (weakenC Γ) A → Term Γ (clock-q A)
    unbox-q : {Γ : Context ∅} {A : Type κ} → Term Γ (clock-q A) → Term (weakenC Γ) A
    next : {Γ : Context κ} {A : Type κ} → Term Γ A → Term Γ (later A)
    _⊛_ : {Γ : Context κ} {A B : Type κ}
      → Term Γ (later (A ⟶ B)) → Term Γ (later A) → Term Γ (later B)
    fix-tm : {Γ : Context κ} {A : Type κ} → Term Γ (later A ⟶ A) → Term Γ A
    force : {Γ : Context ∅} {A : Type κ} → Term Γ (clock-q(later A)) → Term Γ (clock-q A)
    cons : ∀ {Δ} {Γ : Context Δ} (P : Poly Δ) → Term Γ (evalP P (μ P)) → Term Γ (μ P)
    primrec : ∀ {Δ} (P : Poly Δ) {Γ : Context Δ} {A : Type Δ}
      → Term Γ ((evalP P (μ P) ⊠ evalP P A) ⟶ A) → Term Γ (μ P ⟶ A)
    □const : {Γ : Context ∅} (A : Type ∅) → Term Γ (clock-q (weakenT A) ⟶ A)
    □sum : {Γ : Context ∅} (A B : Type κ)
      → Term Γ (clock-q (A ⊞ B) ⟶ (clock-q A ⊞ clock-q B))
    ⟶weaken : (A B : Type ∅)
      → Term • (((weakenT A) ⟶ (weakenT B)) ⟶ weakenT(A ⟶ B))
    μweaken : (P : Poly ∅) → Term • (weakenT (μ P) ⟶ μ (weakenP P))
    weakenμ : (P : Poly ∅) → Term • (μ (weakenP P) ⟶ weakenT (μ P))
\end{code}

\begin{code}
  data Subst : ∀ {Δ} → Context Δ → Context Δ → Set where
    ε : ∀ {Δ} (Γ : Context Δ) → Subst Γ •
    idsub : ∀ {Δ} (Γ : Context Δ) → Subst Γ Γ
    _,s_ : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {A : Type Δ}
      → Subst Γ₁ Γ₂ → Term Γ₁ A → Subst Γ₁ (Γ₂ , A)
    _o_ : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Context Δ} → Subst Γ₂ Γ₃ → Subst Γ₁ Γ₂ → Subst Γ₁ Γ₃
    pr : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {A : Type Δ} → Subst Γ₁ (Γ₂ , A) → Subst Γ₁ Γ₂
    weakenS : {Γ₁ Γ₂ : Context ∅} → Subst Γ₁ Γ₂ → Subst (weakenC Γ₁) (weakenC Γ₂)
    •-to-weaken : Subst • (weakenC •)
    ,-weaken : (Γ : Context ∅) (A : Type ∅)
      → Subst (weakenC Γ , weakenT A) (weakenC (Γ , A))
\end{code}



\AgdaHide{
\begin{code}
weaken-to-• : Subst (weakenC •) •
weaken-to-• = ε (weakenC •)

weaken-, : (Γ : Context ∅) (A : Type ∅) → Subst (weakenC (Γ , A)) (weakenC Γ , weakenT A)
weaken-, Γ A = weakenS (pr (idsub (Γ , A))) ,s ⇡ (varTm Γ A)

weakenSA : ∀ {Δ} {Γ Γ' : Context Δ} (A : Type Δ) → Subst Γ Γ' → Subst (Γ , A) (Γ' , A)
weakenSA {_} {Γ} {Γ'} A s = (s o pr (idsub (Γ , A))) ,s varTm Γ A

bool : Type ∅
bool = 𝟙 ⊞ 𝟙

TRUE : Term • bool
TRUE = in₁ 𝟙 tt

FALSE : Term • bool
FALSE = in₂ 𝟙 tt

weakenTm  : ∀ {Δ} (Γ : Context Δ) (A B : Type Δ) → Term Γ B → Term (Γ , A) B
weakenTm Γ A B x = sub x (pr (idsub (Γ , A)))

app-map : ∀ {Δ} {Γ : Context Δ} {A B : Type Δ} → Term Γ (A ⟶ B) → Term Γ A → Term Γ B
app-map {_} {Γ} {A} {B} f x = sub (appTm f) (idsub Γ ,s x)

idmap : ∀ {Δ} {Γ : Context Δ} (A : Type Δ) → Term Γ (A ⟶ A)
idmap {_} {Γ} A = lambdaTm (varTm Γ A)

⊞map : ∀ {Δ} {Γ : Context Δ} {A₁ B₁ A₂ B₂ : Type Δ}
  → Term Γ (A₁ ⟶ A₂) → Term Γ (B₁ ⟶ B₂) → Term Γ ((A₁ ⊞ B₁) ⟶ (A₂ ⊞ B₂))
⊞map {Δ} {Γ} {A₁} {B₁} {A₂} {B₂} f g =
  lambdaTm (⊞rec (A₂ ⊞ B₂)
                 (in₁ B₂ (app-map (weakenTm Γ A₁ (A₁ ⟶ A₂) f) (varTm Γ A₁)))
                 (in₂ A₂ (app-map (weakenTm Γ B₁ (B₁ ⟶ B₂) g) (varTm Γ B₁))))

⊠map : ∀ {Δ} {Γ : Context Δ} {A₁ B₁ A₂ B₂ : Type Δ}
  → Term Γ (A₁ ⟶ A₂) → Term Γ (B₁ ⟶ B₂) → Term Γ ((A₁ ⊠ B₁) ⟶ (A₂ ⊠ B₂))
⊠map {Δ} {Γ} {A₁} {B₁} {A₂} {B₂} f g =
  lambdaTm [ app-map (weakenTm Γ (A₁ ⊠ B₁) (A₁ ⟶ A₂) f) (π₁ (varTm Γ (A₁ ⊠ B₁)))
           & app-map (weakenTm Γ (A₁ ⊠ B₁) (B₁ ⟶ B₂) g) (π₂ (varTm Γ (A₁ ⊠ B₁))) ]

►map : {Γ : Context κ} {A B : Type κ}
  → Term Γ (A ⟶ B) → Term Γ (later A ⟶ later B)
►map {Γ} {A} {B} f =
  lambdaTm (weakenTm Γ (later A) (later (A ⟶ B)) (next f) ⊛ varTm Γ (later A))

Pmap : ∀ {Δ} (P : Poly Δ) {Γ : Context Δ} {A B : Type Δ}
  → Term Γ (A ⟶ B) → Term Γ (evalP P A ⟶ evalP P B)
Pmap (∁ X) f = idmap X
Pmap I f = f
Pmap (P ⊞ Q) f = ⊞map (Pmap P f) (Pmap Q f)
Pmap (P ⊠ Q) f = ⊠map (Pmap P f) (Pmap Q f)
Pmap (► P) f = ►map (Pmap P f)

compmap : ∀ {Δ} {Γ : Context Δ} {A B C : Type Δ} → Term Γ ((B ⟶ C) ⟶ ((A ⟶ B) ⟶ (A ⟶ C)))
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

split-prod : ∀ {Δ} (Γ : Context Δ) (A B C : Type Δ)
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
subst-μ-help : ∀ {Δ} (Γ : Context Δ) (A B : Type Δ)
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
  data _∼_ : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} → Term Γ A → Term Γ A → Set where -- \sim
    refl∼ : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} {t : Term Γ A} → t ∼ t
    sym∼ : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} {t₁ t₂ : Term Γ A} → t₁ ∼ t₂ → t₂ ∼ t₁
    trans∼ : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} {t₁ t₂ t₃ : Term Γ A} → t₁ ∼ t₂ → t₂ ∼ t₃ → t₁ ∼ t₃
    cong-sub : ∀ {Δ} {Γ Γ' : Context Δ} {A : Type Δ} {t₁ t₂ : Term Γ' A} {s₁ s₂ : Subst Γ Γ'} → t₁ ∼ t₂ → s₁ ≈ s₂ → sub t₁ s₁ ∼ sub t₂ s₂
    cong-unit-rec  : {Γ : Context ∅} {A : Type ∅} {t₁ t₂ : Term Γ A} → t₁ ∼ t₂ → unit-rec t₁ ∼ unit-rec t₂
    cong-in₁ : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} (B : Type Δ) {t₁ t₂ : Term Γ A} → t₁ ∼ t₂ → in₁ A t₁ ∼ in₁ A t₂
    cong-in₂ : ∀ {Δ} {Γ : Context Δ} (A : Type Δ) {B : Type Δ} {t₁ t₂ : Term Γ B} → t₁ ∼ t₂ → in₂ B t₁ ∼ in₂ B t₂
    cong-⊞rec : ∀ {Δ} {Γ : Context Δ} {A B : Type Δ} (C : Type Δ) {t₁ t₂ : Term (Γ , A) C} {u₁ u₂ : Term (Γ , B) C}
      → t₁ ∼ t₂ → u₁ ∼ u₂ → ⊞rec C t₁ u₁ ∼ ⊞rec C t₂ u₂
    cong-[_&_] : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} {t₁ t₂ : Term Γ A} {u₁ u₂ : Term Γ B}
      → t₁ ∼ t₂ → u₁ ∼ u₂ → [ t₁ & u₁ ] ∼ [ t₂ & u₂ ]
    cong-π₁ : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} {t₁ t₂ : Term Γ (A ⊠ B)} → t₁ ∼ t₂ → π₁ t₁ ∼ π₁ t₂
    cong-π₂ : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} {t₁ t₂ : Term Γ (A ⊠ B)} → t₁ ∼ t₂ → π₂ t₁ ∼ π₂ t₂
    cong-lambdaTm : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} {t₁ t₂ : Term (Γ , A) B} → t₁ ∼ t₂ → lambdaTm t₁ ∼ lambdaTm t₂
    cong-appTm  : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} {B : Type Δ} {t₁ t₂ : Term Γ (A ⟶ B)} → t₁ ∼ t₂ → appTm t₁ ∼ appTm t₂
    cong-⇡ : {Γ : Context ∅} {A : Type ∅} {t₁ t₂ : Term Γ A} → t₁ ∼ t₂ → ⇡ t₁ ∼ ⇡ t₂
    cong-↓ : {Γ : Context ∅} {A : Type ∅} {t₁ t₂ : Term (weakenC Γ) (weakenT A)} → t₁ ∼ t₂ → ↓ t₁ ∼ ↓ t₂
    cong-box-q : {Γ : Context ∅} {A : Type κ} {t₁ t₂ : Term (weakenC Γ) A} → t₁ ∼ t₂ → box-q t₁ ∼ box-q t₂
    cong-unbox-q : {Γ : Context ∅} {A : Type κ} {t₁ t₂ : Term Γ (clock-q A)} → t₁ ∼ t₂ → unbox-q t₁ ∼ unbox-q t₂
    cong-next : {Γ : Context κ} {A : Type κ} {t₁ t₂ : Term Γ A} → t₁ ∼ t₂ → next t₁ ∼ next t₂
    cong-_⊛_ : {Γ : Context κ} {A B : Type κ} {t₁ t₂ : Term Γ (later (A ⟶ B))} {u₁ u₂ : Term Γ (later A)} → t₁ ∼ t₂ → u₁ ∼ u₂ → t₁ ⊛ u₁ ∼ t₂ ⊛ u₂
    cong-fix-tm  : {Γ : Context κ} {A : Type κ} {t₁ t₂ : Term Γ (later A ⟶ A)} → t₁ ∼ t₂ → fix-tm t₁ ∼ fix-tm t₂
    cong-force : {Γ : Context ∅} {A : Type κ} {t₁ t₂ : Term Γ (clock-q(later A))} → t₁ ∼ t₂ → force t₁ ∼ force t₂
    cong-cons : ∀ {Δ} {Γ : Context Δ} {P : Poly Δ} {t₁ t₂ : Term Γ (evalP P (μ P))} → t₁ ∼ t₂ → cons P t₁ ∼ cons P t₂
    cong-primrec : ∀ {Δ} (P : Poly Δ) {Γ : Context Δ} {A : Type Δ} {t₁ t₂ : Term Γ ((evalP P (μ P) ⊠ evalP P A) ⟶ A)}
      → t₁ ∼ t₂ → primrec P t₁ ∼ primrec P t₂
    λ-β : ∀ {Δ} {Γ : Context Δ} {A B : Type Δ} (t : Term (Γ , A) B) → appTm (lambdaTm t) ∼ t
    λ-η : ∀ {Δ} {Γ : Context Δ} {A B : Type Δ} (t : Term Γ (A ⟶ B)) → lambdaTm (appTm t) ∼ t
    ⊠-β₁ : ∀ {Δ} {Γ : Context Δ} {A B : Type Δ} (t₁ : Term Γ A) (t₂ : Term Γ B) → π₁ [ t₁ & t₂ ] ∼ t₁
    ⊠-β₂ : ∀ {Δ} {Γ : Context Δ} {A B : Type Δ} (t₁ : Term Γ A) (t₂ : Term Γ B) → π₂ [ t₁ & t₂ ] ∼ t₂
    ⊠-η : ∀ {Δ} {Γ : Context Δ} {A B : Type Δ} (t : Term Γ (A ⊠ B)) → [ π₁ t & π₂ t ] ∼ t
    ⊞-β₁ : ∀ {Δ} {Γ : Context Δ} {A B C : Type Δ} (l : Term (Γ , A) C) (r : Term (Γ , B) C) (t : Term Γ A)
        → sub (⊞rec C l r) (idsub Γ ,s in₁ B t) ∼ sub l (idsub Γ ,s t)
    ⊞-β₂ : ∀ {Δ} {Γ : Context Δ} {A B C : Type Δ} (l : Term (Γ , A) C) (r : Term (Γ , B) C) (t : Term Γ B)
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
    primrec-cons : ∀ {Δ} (P : Poly Δ) {Γ : Context Δ} {A : Type Δ} (t : Term Γ ((evalP P (μ P) ⊠ evalP P A) ⟶ A)) (a : Term Γ (evalP P (μ P)))
      → app-map (primrec P t) (cons P a) ∼ app-map t [ a & app-map (Pmap P (primrec P t)) a ]
    sub-id : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} (t : Term Γ A)
      → sub t (idsub Γ) ∼ t
    sub-sub : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Context Δ} {A : Type Δ} (t : Term Γ₁ A) (s : Subst Γ₂ Γ₁) (s' : Subst Γ₃ Γ₂)
      → sub (sub t s) s' ∼ sub t (s o s')
    sub-varTm : ∀ {Δ} (Γ₁ Γ₂ : Context Δ) (A : Type Δ) (s : Subst Γ₂ Γ₁)
      → sub (varTm Γ₁ A) (weakenSA A s) ∼ varTm Γ₂ A
    sub-unit-rec : {Γ₁ Γ₂ : Context ∅} {A : Type ∅} (t : Term Γ₁ A) (s : Subst Γ₂ Γ₁)
      → sub (unit-rec t) (weakenSA 𝟙 s) ∼ unit-rec (sub t s)
    sub-in₁ : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {A : Type Δ} (B : Type Δ) (t : Term Γ₁ A) (s : Subst Γ₂ Γ₁)
      → sub (in₁ B t) s ∼ in₁ B (sub t s)
    sub-in₂ : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} (A : Type Δ) {B : Type Δ} (t : Term Γ₁ B) (s : Subst Γ₂ Γ₁)
      → sub (in₂ B t) s ∼ in₂ B (sub t s)
    sub-[_&_] : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {A : Type Δ} {B : Type Δ} (t₁ : Term Γ₁ A) (t₂ : Term Γ₁ B) (s : Subst Γ₂ Γ₁)
      → sub [ t₁ & t₂ ] s ∼ [ sub t₁ s & sub t₂ s ]
    sub-lambdaTm : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {A : Type Δ} {B : Type Δ} (t : Term (Γ₁ , A) B) (s : Subst Γ₂ Γ₁)
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
    sub-cons : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {P : Poly Δ} (t : Term Γ₁ (evalP P (μ P))) (s : Subst Γ₂ Γ₁)
      → sub (cons P t) s ∼ cons P (sub t s)
    sub-primrec : ∀ {Δ} (P : Poly Δ) {Γ₁ Γ₂ : Context Δ} {A : Type Δ} (t : Term Γ₁ ((evalP P (μ P) ⊠ evalP P A) ⟶ A)) (s : Subst Γ₂ Γ₁)
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
    μweakenμ : (P : Poly ∅) (t : Term • (μ (weakenP P)))
      → app-map (μweaken P) (app-map (weakenμ P) t) ∼ t
    weakenμweaken : (P : Poly ∅) (t : Term • (weakenT (μ P)))
      → app-map (weakenμ P) (app-map (μweaken P) t) ∼ t
    ⇡↓ : {Γ : Context ∅} {A : Type ∅} (t : Term (weakenC Γ) (weakenT A)) → ⇡(↓ t) ∼ t
    ↓⇡ : {Γ : Context ∅} {A : Type ∅} (t : Term Γ A) → ↓(⇡ t) ∼ t
    ⇡varTm : (Γ : Context ∅) (A : Type ∅) → ⇡(varTm Γ A) ∼ sub (varTm (weakenC Γ) (weakenT A)) (weaken-, Γ A)
    ↓varTm : (Γ : Context ∅) (A : Type ∅) → ↓(sub (varTm (weakenC Γ) (weakenT A)) (weaken-, Γ A)) ∼ varTm Γ A
    ⇡sub : {Γ Γ' : Context ∅} {A : Type ∅} (t : Term Γ' A) (s : Subst Γ Γ') → ⇡(sub t s) ∼ sub (⇡ t) (weakenS s)
    ↓sub : {Γ Γ' : Context ∅} {A : Type ∅} (t : Term (weakenC Γ') (weakenT A)) (s : Subst Γ Γ') → ↓(sub t (weakenS s)) ∼ sub (↓ t) s
    ⇡π₁ : {Γ : Context ∅} {A : Type ∅} {B : Type ∅} (t : Term Γ (A ⊠ B)) → ⇡(π₁ t) ∼ π₁ (app-map (sub (weaken⊠ _ _) (ε (weakenC Γ))) (⇡ t))
    ⇡π₂ : {Γ : Context ∅} {A : Type ∅} {B : Type ∅} (t : Term Γ (A ⊠ B)) → ⇡(π₂ t) ∼ π₂ (app-map (sub (weaken⊠ _ _) (ε (weakenC Γ))) (⇡ t))
    ↓π₁ : {Γ : Context ∅} {A : Type ∅} {B : Type ∅} (t : Term (weakenC Γ) (weakenT (A ⊠ B))) → π₁(↓ t) ∼ ↓(π₁(app-map (sub (weaken⊠ _ _) (ε (weakenC Γ))) t))
    ↓π₂ : {Γ : Context ∅} {A : Type ∅} {B : Type ∅} (t : Term (weakenC Γ) (weakenT (A ⊠ B))) → π₂(↓ t) ∼ ↓(π₂(app-map (sub (weaken⊠ _ _) (ε (weakenC Γ))) t))
    ⇡pair : {Γ : Context ∅} {A : Type ∅} {B : Type ∅} (t₁ : Term Γ A) (t₂ : Term Γ B) → ⇡ [ t₁ & t₂ ] ∼ app-map (sub (⊠weaken _ _) (ε (weakenC Γ))) [ ⇡ t₁ & ⇡ t₂ ]
    ↓pair : {Γ : Context ∅} {A : Type ∅} {B : Type ∅} (t₁ : Term (weakenC Γ) (weakenT A)) (t₂ : Term (weakenC Γ) (weakenT B))
      → [ ↓ t₁ & ↓ t₂ ] ∼ ↓ (app-map (sub (⊠weaken _ _) (ε (weakenC Γ))) [ t₁ & t₂ ])
    ⇡in₁ : {Γ : Context ∅} {A : Type ∅} {B : Type ∅} (t : Term Γ A) → ⇡(in₁ B t) ∼ app-map (sub (⊞weaken _ _) (ε (weakenC Γ))) (in₁ (weakenT B) (⇡ t))
    ⇡in₂ : {Γ : Context ∅} {A : Type ∅} {B : Type ∅} (t : Term Γ B) → ⇡(in₂ A t) ∼ app-map (sub (⊞weaken _ _) (ε (weakenC Γ))) (in₂ (weakenT A) (⇡ t))
    ↓in₁ : {Γ : Context ∅} {A : Type ∅} {B : Type ∅} (t : Term (weakenC Γ) (weakenT A)) → in₁ B (↓ t) ∼ ↓(app-map (sub (⊞weaken _ _) (ε (weakenC Γ))) (in₁ (weakenT B) t))
    ↓in₂ : {Γ : Context ∅} {A : Type ∅} {B : Type ∅} (t : Term (weakenC Γ) (weakenT B)) → in₂ A (↓ t) ∼ ↓(app-map (sub (⊞weaken _ _) (ε (weakenC Γ))) (in₂ (weakenT A) t))
    ⇡⊞rec : {Γ : Context ∅} {A B : Type ∅} (C : Type ∅) (l : Term (Γ , A) C) (r : Term (Γ , B) C)
      → ⇡(⊞rec C l r)
        ∼
        sub (⊞rec (weakenT C)
                  (sub (⇡ l) (,-weaken Γ A))
                  (sub (⇡ r) (,-weaken Γ B)))
            ((pr (idsub (weakenC Γ , weakenT (A ⊞ B))) ,s app-map (sub (weaken⊞ _ _) (ε (weakenC Γ , weakenT (A ⊞ B)))) (varTm (weakenC Γ) (weakenT (A ⊞ B)))) o weaken-, Γ (A ⊞ B))
    ↓⊞rec : {Γ : Context ∅} {A B : Type ∅} (C : Type ∅) (l : Term (weakenC (Γ , A)) (weakenT C)) (r : Term (weakenC (Γ , B)) (weakenT C))
      → ⊞rec C (↓ l) (↓ r)
        ∼
        ↓ (sub (⊞rec (weakenT C) (sub l (,-weaken Γ A)) (sub r (,-weaken Γ B)))
               (weakenS (pr (idsub (Γ , (A ⊞ B)))) ,s app-map (sub (weaken⊞ _ _) (ε (weakenC (Γ , (A ⊞ B))))) (⇡ (varTm Γ (A ⊞ B)))))
    ⇡lambda : {Γ : Context ∅} {A B : Type ∅} (t : Term (Γ , A) B) → ⇡ (lambdaTm t) ∼ app-map (sub (⟶weaken _ _) (ε (weakenC Γ))) (lambdaTm (sub (⇡ t) (,-weaken Γ A)))
    ↓lambda : {Γ : Context ∅} {A B : Type ∅} (t : Term (weakenC (Γ , A)) (weakenT B)) → lambdaTm (↓ t) ∼ ↓ (app-map (sub (⟶weaken _ _) (ε (weakenC Γ))) (lambdaTm (sub t (,-weaken Γ A))))
    ⇡app : {Γ : Context ∅} {A B : Type ∅} (t : Term Γ (A ⟶ B)) → ⇡ (appTm t) ∼ sub (appTm (app-map (sub (weaken⟶ _ _) (ε (weakenC Γ))) (⇡ t))) (weaken-, Γ A)
    ↓app : {Γ : Context ∅} {A B : Type ∅} (t : Term (weakenC Γ) (weakenT (A ⟶ B))) → appTm (↓ t) ∼ ↓ (sub (appTm (app-map (sub (weaken⟶ _ _) (ε (weakenC Γ))) t)) (weaken-, Γ A))

  data _≈_ : ∀ {Δ} {Γ Γ' : Context Δ} → Subst Γ Γ' → Subst Γ Γ' → Set where -- ≈
    refl≈ : ∀ {Δ} {Γ Γ' : Context Δ} {s : Subst Γ Γ'} → s ≈ s
    sym≈ : ∀ {Δ} {Γ Γ' : Context Δ} {s₁ s₂ : Subst Γ Γ'} → s₁ ≈ s₂ → s₂ ≈ s₁
    trans≈ : ∀ {Δ} {Γ Γ' : Context Δ} {s₁ s₂ s₃ : Subst Γ Γ'} → s₁ ≈ s₂ → s₂ ≈ s₃ → s₁ ≈ s₃
    cong-_,s_ : ∀ {Δ} {Γ Γ' : Context Δ} {A : Type Δ} {s₁ s₂ : Subst Γ Γ'} {t₁ t₂ : Term Γ A} → s₁ ≈ s₂ → t₁ ∼ t₂ → s₁ ,s t₁ ≈ s₂ ,s t₂
    cong-_o_ : ∀ {Δ} {Γ Γ' Γ'' : Context Δ} {s₁ s₂ : Subst Γ' Γ''} {σ₁ σ₂ : Subst Γ Γ'} → s₁ ≈ s₂ → σ₁ ≈ σ₂ → s₁ o σ₁ ≈ s₂ o σ₂
    cong-pr : ∀ {Δ} {Γ Γ' : Context Δ} {A : Type Δ} {s₁ s₂ : Subst Γ (Γ' , A)} → s₁ ≈ s₂ → pr s₁ ≈ pr s₂
    sub-idl : ∀ {Δ} {Γ Γ' : Context Δ} (s : Subst Γ Γ') → idsub Γ' o s ≈ s
    sub-idr : ∀ {Δ} {Γ Γ' : Context Δ} (s : Subst Γ Γ') → s o idsub Γ ≈ s
    sub-assoc : ∀ {Δ} {Γ₁ Γ₂ Γ₃ Γ₄ : Context Δ} (s₁ : Subst Γ₁ Γ₂) (s₂ : Subst Γ₂ Γ₃) (s₃ : Subst Γ₃ Γ₄)
      → s₃ o (s₂ o s₁) ≈ (s₃ o s₂) o s₁
    sub-π₁β : ∀ {Δ} {Γ Γ' : Context Δ} {A : Type Δ} {t : Term Γ A} (s : Subst Γ Γ')
      → pr (s ,s t) ≈ s
    sub-εη : ∀ {Δ} {Γ : Context Δ} (s : Subst Γ •) → s ≈ ε Γ
    sub-,o : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Context Δ} {A : Type Δ} {t : Term Γ₂ A} (s₁ : Subst Γ₁ Γ₂) (s₂ : Subst Γ₂ Γ₃)
      → (s₂ ,s t) o s₁ ≈ (s₂ o s₁) ,s sub t s₁
    sub-η : ∀ {Δ} {Γ : Context Δ} {A : Type Δ} (s : Subst Γ (Γ , A))
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
\end{code}
}
