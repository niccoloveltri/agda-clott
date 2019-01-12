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
open ►Obj
open ExpObj
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
  ⟦ ▻P P ⟧poly = ►P ⟦ P ⟧poly

  ⟦_⟧A : {Δ : ClockContext} → Type Δ → Ty ⟦ Δ ⟧Δ
  ⟦ 𝟙 ⟧A = Unit
  ⟦ A ⊞ B ⟧A = ⟦ A ⟧A ⊕ ⟦ B ⟧A
  ⟦ A ⊠ B ⟧A = ⟦ A ⟧A ⊗ ⟦ B ⟧A
  ⟦ A ⟶ B ⟧A = ⟦ A ⟧A ⇒ ⟦ B ⟧A
  ⟦ weakenT A ⟧A = WC ⟦ A ⟧A
  ⟦ ▻ A ⟧A = ►(⟦ A ⟧A)
  ⟦ □ A ⟧A = ■(⟦ A ⟧A)
  ⟦ μ P ⟧A = mu ⟦ P ⟧poly  
  
⟦_⟧Γ : {Δ : ClockContext} → Context Δ → Ctx ⟦ Δ ⟧Δ
⟦ • ⟧Γ = ∙ _
⟦ Γ , A ⟧Γ = (⟦ Γ ⟧Γ) ,, ⟦ A ⟧A
⟦ weakenC Γ ⟧Γ = WC ⟦ Γ ⟧Γ

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
cons₁' P (▻P Q) i t = ►P c₁ c₂
  where
    c₁ : Later (μObj' ⟦ P ⟧poly ⟦ Q ⟧poly) i
    c₁ [ j ] = cons₁' P Q j (►cone t [ j ])
    c₂ : LaterLim (μObj' ⟦ P ⟧poly ⟦ Q ⟧poly) (μMor' ⟦ P ⟧poly ⟦ Q ⟧poly) i c₁
    c₂ [ j ] [ k ] = trans (cons₂' P Q j k (►cone t [ j ])) (cong (cons₁' P Q k) (►com t [ j ] [ k ]))
cons₂' P (∁ X) i j t = refl
cons₂' P I i j t = refl
cons₂' P (Q ⊠ R) i j (t , u) = cong₂ _⊠_ (cons₂' P Q i j t) (cons₂' P R i j u)
cons₂' P (Q ⊞ R) i j (inj₁ t) = cong ⊞₁ (cons₂' P Q i j t)
cons₂' P (Q ⊞ R) i j (inj₂ t) = cong ⊞₂ (cons₂' P R i j t)
cons₂' P (▻P Q) i j t =
  cong₂-dep ►P (funext (λ { [ _ ] → refl})) (funext (λ { [ _ ] → funext (λ { [ _ ] → uip }) }))

conspsh : (P Q : Poly κ) (Γ : Context κ) → Tm ⟦ Γ ⟧Γ ⟦ evalP Q (μ P) ⟧A → Tm ⟦ Γ ⟧Γ (μpsh ⟦ P ⟧poly ⟦ Q ⟧poly)
proj₁ (conspsh P Q Γ (t , p)) i γ  = cons₁' P Q i (t i γ)
proj₂ (conspsh P Q Γ (t , p)) i j γ = trans (cons₂' P Q i j (t i γ)) (cong (cons₁' P Q j) (p i j γ))


primrec-set' : (P Q : Poly ∅) (A : Type ∅)
  → ⟦ (evalP P (μ P) ⊠ evalP P A) ⟶ A ⟧A
  → (μset ⟦ P ⟧poly ⟦ Q ⟧poly)
  → (⟦ evalP Q (μ P) ⊠ evalP Q A ⟧A)
primrec-set' P (∁ X) A y (∁s z) = z , z
primrec-set' P I A y (I z) = z , y (primrec-set' P P A y z)
primrec-set' P (Q₁ ⊞ Q₂) A y (⊞₁ z) = inj₁ (proj₁ (primrec-set' P Q₁ A y z)) , inj₁ (proj₂ (primrec-set' P Q₁ A y z))
primrec-set' P (Q₁ ⊞ Q₂) A y (⊞₂ z) = inj₂ (proj₁ (primrec-set' P Q₂ A y z)) , inj₂ (proj₂ (primrec-set' P Q₂ A y z))
proj₁ (proj₁ (primrec-set' P (Q₁ ⊠ Q₂) A y (z₁ ⊠ z₂))) = proj₁ (primrec-set' P Q₁ A y z₁) 
proj₂ (proj₁ (primrec-set' P (Q₁ ⊠ Q₂) A y (z₁ ⊠ z₂))) = proj₁ (primrec-set' P Q₂ A y z₂)
proj₁ (proj₂ (primrec-set' P (Q₁ ⊠ Q₂) A y (z₁ ⊠ z₂))) = proj₂ (primrec-set' P Q₁ A y z₁)
proj₂ (proj₂ (primrec-set' P (Q₁ ⊠ Q₂) A y (z₁ ⊠ z₂))) = proj₂ (primrec-set' P Q₂ A y z₂)

primrec-set : (P : Poly ∅) (Γ : Context ∅) (A : Type ∅)
  → Tm ⟦ Γ ⟧Γ ⟦ (evalP P (μ P) ⊠ evalP P A) ⟶ A ⟧A
  → Tm ⟦ Γ ⟧Γ (mu ⟦ P ⟧poly ⇒ ⟦ A ⟧A)
primrec-set P Γ A t x a = t x (primrec-set' P P A (t x) a)

primrec-psh'₁₁ : (P Q : Poly κ) (A : Type κ) (i : Size) (t : Obj ⟦ (evalP P (μ P) ⊠ evalP P A) ⟶ A ⟧A i)
  → (j : Size< (↑ i)) (z : μObj' ⟦ P ⟧poly ⟦ Q ⟧poly j)
  → Obj ⟦ evalP Q (μ P) ⊠ evalP Q A ⟧A j
primrec-psh'₁₂ : (P Q : Poly κ) (A : Type κ) (i : Size) (t : Obj ⟦ (evalP P (μ P) ⊠ evalP P A) ⟶ A ⟧A i)
  → (j : Size< (↑ i)) (z : μObj' ⟦ P ⟧poly ⟦ Q ⟧poly j) (k : Size< (↑ j))
  → Mor ⟦ evalP Q (μ P) ⊠ evalP Q A ⟧A j k (primrec-psh'₁₁ P Q A i t j z)
    ≡
    primrec-psh'₁₁ P Q A i t k (μMor' ⟦ P ⟧poly ⟦ Q ⟧poly j k z)
proj₁ (primrec-psh'₁₁ P (∁ X) A i t j (∁ps z)) = z
proj₂ (primrec-psh'₁₁ P (∁ X) A i t j (∁ps z)) = z
primrec-psh'₁₁ P I A i t j (I z) = (z , fun t j (primrec-psh'₁₁ P P A i t j z))
primrec-psh'₁₁ P (Q₁ ⊞ Q₂) A i t j (⊞₁ z) = (inj₁ (proj₁ (primrec-psh'₁₁ P Q₁ A i t j z)) , inj₁ (proj₂ (primrec-psh'₁₁ P Q₁ A i t j z)))
primrec-psh'₁₁ P (Q₁ ⊞ Q₂) A i t j (⊞₂ z) = (inj₂ (proj₁ (primrec-psh'₁₁ P Q₂ A i t j z)) , inj₂ (proj₂ (primrec-psh'₁₁ P Q₂ A i t j z)))
primrec-psh'₁₁ P (Q₁ ⊠ Q₂) A i t j (z₁ ⊠ z₂) =
  ((proj₁ (primrec-psh'₁₁ P Q₁ A i t j z₁) , proj₁ (primrec-psh'₁₁ P Q₂ A i t j z₂)),
   (proj₂ (primrec-psh'₁₁ P Q₁ A i t j z₁) , proj₂ (primrec-psh'₁₁ P Q₂ A i t j z₂)))
►cone (proj₁ (primrec-psh'₁₁ P (▻P Q) A i t j (►P z₁ z₂))) [ k ] = proj₁ (primrec-psh'₁₁ P Q A i t k (z₁ [ k ]))
►com (proj₁ (primrec-psh'₁₁ P (▻P Q) A i t j (►P z₁ z₂))) [ k ] [ l ] =
  trans (cong proj₁ (primrec-psh'₁₂ P Q A i t k (z₁ [ k ]) l))
        ((cong (λ q → proj₁ (primrec-psh'₁₁ P Q A i t l q)) (z₂ [ k ] [ l ])))
►cone (proj₂ (primrec-psh'₁₁ P (▻P Q) A i t j (►P z₁ z₂))) [ k ] = proj₂ (primrec-psh'₁₁ P Q A i t k (z₁ [ k ]))
►com (proj₂ (primrec-psh'₁₁ P (▻P Q) A i t j (►P z₁ z₂))) [ k ] [ l ] =
  trans (cong proj₂ (primrec-psh'₁₂ P Q A i t k (z₁ [ k ]) l))
        ((cong (λ q → proj₂ (primrec-psh'₁₁ P Q A i t l q)) (z₂ [ k ] [ l ])))
primrec-psh'₁₂ P (∁ X) A i t j (∁ps z) k = refl
primrec-psh'₁₂ P I A i f j (I z) k =
  cong (λ z → (_ , z))
       (trans (funcom f j k (primrec-psh'₁₁ P P A i f j z))
              ((cong (fun f k) (primrec-psh'₁₂ P P A i f j z k))))
primrec-psh'₁₂ P (Q₁ ⊞ Q₂) A i t j (⊞₁ z) k =
  cong₂ (_,_)
        (cong (λ z → inj₁(proj₁ z)) (primrec-psh'₁₂ P Q₁ A i t j z k))
        (cong (λ z → inj₁(proj₂ z)) (primrec-psh'₁₂ P Q₁ A i t j z k))
primrec-psh'₁₂ P (Q₁ ⊞ Q₂) A i t j (⊞₂ z) k =
  cong₂ (_,_)
        (cong (λ z → inj₂(proj₁ z)) (primrec-psh'₁₂ P Q₂ A i t j z k))
        (cong (λ z → inj₂(proj₂ z)) (primrec-psh'₁₂ P Q₂ A i t j z k))
primrec-psh'₁₂ P (Q₁ ⊠ Q₂) A i t j (z₁ ⊠ z₂) k =
  cong₂ (_,_)
        (cong₂ (_,_)
               (cong (λ z → proj₁ z) (primrec-psh'₁₂ P Q₁ A i t j z₁ k))
               (cong (λ z → proj₁ z) (primrec-psh'₁₂ P Q₂ A i t j z₂ k)))
        (cong₂ (_,_)
               (cong (λ z → proj₂ z) (primrec-psh'₁₂ P Q₁ A i t j z₁ k))
               (cong (λ z → proj₂ z) (primrec-psh'₁₂ P Q₂ A i t j z₂ k)))
primrec-psh'₁₂ P (▻P Q) A i t j (►P z₁ z₂) k = cong₂ (_,_) (►eq (λ {_ → refl})) (►eq (λ {_ → refl}))

primrec-psh'₂ : (P Q : Poly κ) (Γ : Ctx tot) (A : Type κ) (t : Tm Γ ⟦ (evalP P (μ P) ⊠ evalP P A) ⟶ A ⟧A)
  → (i : Size) (j : Size< (↑ i)) (x : Obj Γ i) (k : Size< (↑ j)) (z : μObj' ⟦ P ⟧poly ⟦ Q ⟧poly k)
  → primrec-psh'₁₁ P Q A i (proj₁ t i x) k z
    ≡
    primrec-psh'₁₁ P Q A j (proj₁ t j (Mor Γ i j x)) k z
primrec-psh'₂ P (∁ X) Γ A t i j x k (∁ps z) = refl
primrec-psh'₂ P I Γ A t i j x k (I z) =
  cong (λ q → (z , q))
       (trans (cong (λ q → fun q k (primrec-psh'₁₁ P P A i (proj₁ t i x) k z)) (proj₂ t i j x))
              (cong (λ z → fun (proj₁ t j (Mor Γ i j x)) k z) (primrec-psh'₂ P P Γ A t i j x k z)))
primrec-psh'₂ P (Q₁ ⊞ Q₂) Γ A t i j x k (⊞₁ z) =
  cong₂ (_,_)
        (cong inj₁ (cong proj₁ (primrec-psh'₂ P Q₁ Γ A t i j x k z)))
        (cong inj₁ (cong proj₂ (primrec-psh'₂ P Q₁ Γ A t i j x k z)))
primrec-psh'₂ P (Q₁ ⊞ Q₂) Γ A t i j x k (⊞₂ z) =
  cong₂ (_,_)
        (cong inj₂ (cong proj₁ (primrec-psh'₂ P Q₂ Γ A t i j x k z)))
        (cong inj₂ (cong proj₂ (primrec-psh'₂ P Q₂ Γ A t i j x k z)))
primrec-psh'₂ P (Q₁ ⊠ Q₂) Γ A t i j x k (z₁ ⊠ z₂) =
  cong₂ (_,_)
        (cong₂ (_,_)
               (cong proj₁ (primrec-psh'₂ P Q₁ Γ A t i j x k z₁))
               (cong proj₁ (primrec-psh'₂ P Q₂ Γ A t i j x k z₂)))
        (cong₂ (_,_)
               (cong proj₂ (primrec-psh'₂ P Q₁ Γ A t i j x k z₁))
               (cong proj₂ (primrec-psh'₂ P Q₂ Γ A t i j x k z₂)))
primrec-psh'₂ P (▻P Q) Γ A t i j x k (►P z₁ z₂) =
  cong₂ (_,_)
        (►eq (λ {l → cong proj₁ (primrec-psh'₂ P Q Γ A t i j x l (z₁ [ l ]))}))
        (►eq (λ {l → cong proj₂ (primrec-psh'₂ P Q Γ A t i j x l (z₁ [ l ]))}))

primrec-psh : (P : Poly κ) (Γ : Context κ) (A : Type κ)
  → Tm ⟦ Γ ⟧Γ ⟦ (evalP P (μ P) ⊠ evalP P A) ⟶ A ⟧A
  → Tm ⟦ Γ ⟧Γ (mu ⟦ P ⟧poly ⇒ ⟦ A ⟧A)
fun (proj₁ (primrec-psh P Γ A (f , p)) i x) j y = fun (f i x) j (primrec-psh'₁₁ P P A i (f i x) j y) -- proj₁ (f i x) j (primrec-psh'₁₁ P P A i (f i x) j y)
funcom (proj₁ (primrec-psh P Γ A (f , p)) i x) j k y =
  trans (funcom (f i x) j k _)
        (cong (fun (f i x) k) (primrec-psh'₁₂ P P A i (f i x) j y k))
proj₂ (primrec-psh P Γ A t) i j x = funeq (λ k z → cong₂ (λ a b → fun a k b) (proj₂ t i j x) (primrec-psh'₂ P P ⟦ Γ ⟧Γ A t i j x k z))

μweaken-help : (P Q : Poly ∅) → μset ⟦ P ⟧poly ⟦ Q ⟧poly → (i : Size) → μObj' ⟦ weakenP P ⟧poly ⟦ weakenP Q ⟧poly i
μweaken-help P (∁ X) (∁s x) i = ∁ps x
μweaken-help P I (I x) i = I (μweaken-help P P x i)
μweaken-help P (Q₁ ⊞ Q₂) (⊞₁ x) i = ⊞₁ (μweaken-help P Q₁ x i)
μweaken-help P (Q₁ ⊞ Q₂) (⊞₂ x) i = ⊞₂ (μweaken-help P Q₂ x i)
μweaken-help P (Q₁ ⊠ Q₂) (x₁ ⊠ x₂) i = μweaken-help P Q₁ x₁ i ⊠ μweaken-help P Q₂ x₂ i

μweaken-eq : (P Q : Poly ∅) (x : μset ⟦ P ⟧poly ⟦ Q ⟧poly) (i : Size) (j : Size< (↑ i)) (k : Size< (↑ j))
  → μMor' ⟦ weakenP P ⟧poly ⟦ weakenP Q ⟧poly j k
          (μweaken-help P Q x j)
    ≡
    μweaken-help P Q x k
μweaken-eq P (∁ X) (∁s x) i j k = refl
μweaken-eq P I (I x) i j k = cong I (μweaken-eq P P x i j k)
μweaken-eq P (Q₁ ⊞ Q₂) (⊞₁ x) i j k = cong ⊞₁ (μweaken-eq P Q₁ x i j k)
μweaken-eq P (Q₁ ⊞ Q₂) (⊞₂ x) i j k = cong ⊞₂ (μweaken-eq P Q₂ x i j k)
μweaken-eq P (Q₁ ⊠ Q₂) (x₁ ⊠ x₂) i j k =
  cong₂ (_⊠_) (μweaken-eq P Q₁ x₁ i j k) (μweaken-eq P Q₂ x₂ i j k)

weakenμ-help : (P Q : Poly ∅) → (i : Size) → μObj' ⟦ weakenP P ⟧poly ⟦ weakenP Q ⟧poly i → μset ⟦ P ⟧poly ⟦ Q ⟧poly
weakenμ-help P (∁ X) i (∁ps x) = ∁s x
weakenμ-help P I i (I x) = I (weakenμ-help P P i x)
weakenμ-help P (Q₁ ⊞ Q₂) i (⊞₁ x) = ⊞₁ (weakenμ-help P Q₁ i x)
weakenμ-help P (Q₁ ⊞ Q₂) i (⊞₂ x) = ⊞₂ (weakenμ-help P Q₂ i x)
weakenμ-help P (Q₁ ⊠ Q₂) i (x₁ ⊠ x₂) = weakenμ-help P Q₁ i x₁ ⊠ weakenμ-help P Q₂ i x₂

weakenμ-eq : (P Q : Poly ∅) (i : Size) (x : μObj' ⟦ weakenP P ⟧poly ⟦ weakenP Q ⟧poly i) (j : Size< (↑ i))
  → weakenμ-help P Q i x
    ≡
    weakenμ-help P Q j (μMor' ⟦ weakenP P ⟧poly ⟦ weakenP Q ⟧poly i j x)
weakenμ-eq P (∁ X) i (∁ps x) j = refl
weakenμ-eq P I i (I x) j = cong I (weakenμ-eq P P i x j)
weakenμ-eq P (Q₁ ⊞ Q₂) i (⊞₁ x) j = cong ⊞₁ (weakenμ-eq P Q₁ i x j)
weakenμ-eq P (Q₁ ⊞ Q₂) i (⊞₂ x) j = cong ⊞₂ (weakenμ-eq P Q₂ i x j)
weakenμ-eq P (Q₁ ⊠ Q₂) i (x₁ ⊠ x₂) j =
  cong₂ (_⊠_) (weakenμ-eq P Q₁ i x₁ j) (weakenμ-eq P Q₂ i x₂ j)

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
  ⟦ force {Γ} {A} t ⟧tm = sem-force ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ t ⟧tm
  ⟦_⟧tm {∅} {Γ} (cons P t) z = consset' P P (⟦ t ⟧tm z)
  ⟦_⟧tm {κ} {Γ} (cons P t) = conspsh P P Γ ⟦ t ⟧tm
  ⟦_⟧tm {∅} (primrec P {Γ} {A} t) = primrec-set P Γ A ⟦ t ⟧tm
  ⟦_⟧tm {κ} (primrec P {Γ} {A} t) = primrec-psh P Γ A ⟦ t ⟧tm
  ⟦ □const A ⟧tm = ■const-tm _ ⟦ A ⟧A
  ⟦ □sum A B ⟧tm = ■sum-tm _ ⟦ A ⟧A ⟦ B ⟧A
  fun (proj₁ ⟦ ⟶weaken A B ⟧tm i x) j f = fun f j
  funcom (proj₁ ⟦ ⟶weaken A B ⟧tm i x) j k f = funext (funcom f j k) 
  proj₂ ⟦ ⟶weaken A B ⟧tm i j x = funeq (λ _ _ → refl)
  fun (proj₁ ⟦ μweaken P ⟧tm i x) j y = μweaken-help P P y j
  funcom (proj₁ ⟦ μweaken P ⟧tm i x) j k y = μweaken-eq P P y i j k
  proj₂ ⟦ μweaken P ⟧tm i j x = funeq (λ _ _ → refl)
  fun (proj₁ ⟦ weakenμ P ⟧tm i x) j y = weakenμ-help P P j y
  funcom (proj₁ ⟦ weakenμ P ⟧tm i x) j k y = weakenμ-eq P P j y k
  proj₂ ⟦ weakenμ P ⟧tm i j x = funeq (λ _ _ → refl)
\end{code}
