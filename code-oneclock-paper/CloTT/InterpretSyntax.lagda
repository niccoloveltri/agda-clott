\AgdaHide{
\begin{code}
module CloTT.InterpretSyntax where

open import Data.Sum
open import Data.Product
open import Data.Unit
open import Prelude
open import Prelude.Syntax
open import Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers

open PSh
\end{code}
}

\begin{code}
⟦_⟧Δ : ClockContext → tag
⟦ ∅ ⟧Δ = set
⟦ κ ⟧Δ = tot

mutual
  ⟦_⟧poly : {Δ : ClockContext} → Poly Δ → SemPoly ⟦ Δ ⟧Δ
  ⟦_⟧poly {∅} (∁ A) = ∁s ⟦ A ⟧A
  ⟦_⟧poly {κ} (∁ A) = ∁ps ⟦ A ⟧A
  ⟦ I ⟧poly = I
  ⟦ P ⊞ Q ⟧poly = ⟦ P ⟧poly ⊞ ⟦ Q ⟧poly
  ⟦ P ⊠ Q ⟧poly = ⟦ P ⟧poly ⊠ ⟦ Q ⟧poly
  ⟦ ► P ⟧poly = ► ⟦ P ⟧poly

  ⟦_⟧A : {Δ : ClockContext} → Type Δ → Ty ⟦ Δ ⟧Δ
  ⟦ 𝟙 ⟧A = Unit
  ⟦ A ⊞ B ⟧A = ⟦ A ⟧A ⊕ ⟦ B ⟧A
  ⟦ A ⊠ B ⟧A = ⟦ A ⟧A ⊗ ⟦ B ⟧A
  ⟦ A ⟶ B ⟧A = ⟦ A ⟧A ⇒ ⟦ B ⟧A
  ⟦ weakenT A ⟧A = WC ⟦ A ⟧A
  ⟦ later A ⟧A = ▻(⟦ A ⟧A)
  ⟦ clock-q A ⟧A = □(⟦ A ⟧A)
  ⟦ μ P ⟧A = mu ⟦ P ⟧poly  
  
⟦_⟧Γ : {Δ : ClockContext} → Context Δ → Ctx ⟦ Δ ⟧Δ
⟦ • ⟧Γ = ∙ _
⟦ Γ , A ⟧Γ = (⟦ Γ ⟧Γ) ,, ⟦ A ⟧A
⟦ weakenC Γ ⟧Γ = WC ⟦ Γ ⟧Γ

{-
consset' : (P Q : Poly ∅) (Γ : Context ∅) → Tm ⟦ Γ ⟧Γ ⟦ evalP Q (μ P) ⟧A → Tm ⟦ Γ ⟧Γ (μset ⟦ P ⟧poly ⟦ Q ⟧poly)
consset' P (∁ x) Γ t z = ∁s (t z)
consset' P I Γ t z = I (t z)
consset' P (Q ⊞ Q₁) Γ t z with (t z)
consset' P (Q₁ ⊞ Q₂) Γ t z | inj₁ x = ⊞₁ (consset' P Q₁ Γ (λ _ → x) z)
consset' P (Q₁ ⊞ Q₂) Γ t z | inj₂ y = ⊞₂ (consset' P Q₂ Γ (λ _ → y) z)
consset' P (Q₁ ⊠ Q₂) Γ t z =
  consset' P Q₁ Γ (λ z₁ → proj₁ (t z₁)) z ⊠ consset' P Q₂ Γ (λ z₁ → proj₂ (t z₁)) z
-}

consset' : (P Q : Poly ∅) → ⟦ evalP Q (μ P) ⟧A → μset ⟦ P ⟧poly ⟦ Q ⟧poly
consset' P (∁ x) t = ∁s t -- ∁s t
consset' P I t = I t -- I t
consset' P (Q ⊞ Q₁) (inj₁ x) = ⊞₁ (consset' P Q x)
consset' P (Q ⊞ Q₁) (inj₂ y) = ⊞₂ (consset' P Q₁ y)
consset' P (Q₁ ⊠ Q₂) t = consset' P Q₁ (proj₁ t) ⊠ consset' P Q₂ (proj₂ t)

cons₁' : (P Q : Poly κ) (i : Size) → Obj ⟦ evalP Q (μ P) ⟧A i → μObj' ⟦ P ⟧poly ⟦ Q ⟧poly i
cons₂' : (P Q : Poly κ) (i : Size) (j : Size< (↑ i)) (t : Obj ⟦ evalP Q (μ P) ⟧A i)
  → μMor' ⟦ P ⟧poly ⟦ Q ⟧poly i j (cons₁' P Q i t) ≡ cons₁' P Q j (Mor ⟦ evalP Q (μ P) ⟧A i j t)
cons₁' P (∁ X) i t = ∁ps t
cons₁' P I i t = I t
cons₁' P (Q ⊠ R) i (t , u) = (cons₁' P Q i t) ⊠ (cons₁' P R i u)
cons₁' P (Q ⊞ R) i (inj₁ t) = ⊞₁ (cons₁' P Q i t)
cons₁' P (Q ⊞ R) i (inj₂ t) = ⊞₂ (cons₁' P R i t)
cons₁' P (► Q) i (t , p) = ► c₁ c₂
  where
    c₁ : Later (μObj' ⟦ P ⟧poly ⟦ Q ⟧poly) i
    c₁ [ j ] = cons₁' P Q j (t [ j ])
    c₂ : LaterLim (μObj' ⟦ P ⟧poly ⟦ Q ⟧poly) (μMor' ⟦ P ⟧poly ⟦ Q ⟧poly) i c₁
    c₂ [ j ] [ k ] = trans (cons₂' P Q j k (t [ j ])) (cong (cons₁' P Q k) (p [ j ] [ k ]))
cons₂' P (∁ X) i j t = refl
cons₂' P I i j t = refl
cons₂' P (Q ⊠ R) i j (t , u) = cong₂ _⊠_ (cons₂' P Q i j t) (cons₂' P R i j u)
cons₂' P (Q ⊞ R) i j (inj₁ t) = cong ⊞₁ (cons₂' P Q i j t)
cons₂' P (Q ⊞ R) i j (inj₂ t) = cong ⊞₂ (cons₂' P R i j t)
cons₂' P (► Q) i j (t , p) =
  cong₂-dep ► (funext (λ { [ _ ] → refl})) (funext (λ { [ _ ] → funext (λ { [ _ ] → uip }) }))

conspsh : (P Q : Poly κ) (Γ : Context κ) → Tm ⟦ Γ ⟧Γ ⟦ evalP Q (μ P) ⟧A → Tm ⟦ Γ ⟧Γ (μpsh ⟦ P ⟧poly ⟦ Q ⟧poly)
proj₁ (conspsh P Q Γ (t , p)) i γ  = cons₁' P Q i (t i γ)
proj₂ (conspsh P Q Γ (t , p)) i j γ = trans (cons₂' P Q i j (t i γ)) (cong (cons₁' P Q j) (p i j γ))

mutual
  ⟦_⟧sub : {Δ : ClockContext} {Γ Γ' : Context Δ} → Subst Γ Γ' → sem-subst ⟦ Γ ⟧Γ ⟦ Γ' ⟧Γ
  ⟦ ε Γ ⟧sub = sem-ε ⟦ Γ ⟧Γ
  ⟦ idsub Γ ⟧sub = sem-idsub ⟦ Γ ⟧Γ
  ⟦ s ,s x ⟧sub = sem-subst-tm _ _ _ ⟦ s ⟧sub ⟦ x ⟧tm
  ⟦ s o s' ⟧sub = sem-subcomp _ _ _ ⟦ s ⟧sub ⟦ s' ⟧sub
  ⟦ pr {_} {Γ} {Γ'} {A} s ⟧sub = sem-subpr ⟦ Γ ⟧Γ ⟦ Γ' ⟧Γ ⟦ A ⟧A ⟦ s ⟧sub
  proj₁ ⟦ weakenS s ⟧sub i = ⟦ s ⟧sub
  proj₂ ⟦ weakenS s ⟧sub i j x = refl
  proj₁ ⟦ •-to-weaken ⟧sub i tt = tt
  proj₂ ⟦ •-to-weaken ⟧sub i j x = refl
  proj₁ ⟦ ,-weaken Γ A ⟧sub i x = x
  proj₂ ⟦ ,-weaken Γ A ⟧sub i j x = refl
  
  ⟦_⟧tm : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} → Term Γ A → Tm ⟦ Γ ⟧Γ ⟦ A ⟧A
  ⟦ sub t s ⟧tm = sem-sub _ _ _ ⟦ t ⟧tm ⟦ s ⟧sub
  ⟦ varTm Γ A ⟧tm = var ⟦ Γ ⟧Γ ⟦ A ⟧A
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
  ⟦_⟧tm {∅} {Γ} (cons P t) z = consset' P P (⟦ t ⟧tm z)
  ⟦_⟧tm {κ} {Γ} (cons P t) = conspsh P P Γ ⟦ t ⟧tm
  ⟦ □const A ⟧tm = □const-tm _ ⟦ A ⟧A
  ⟦ □sum A B ⟧tm = □sum-tm _ ⟦ A ⟧A ⟦ B ⟧A
\end{code}
