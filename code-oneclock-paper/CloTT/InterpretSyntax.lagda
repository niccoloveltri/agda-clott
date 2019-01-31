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
open NatTrans
\end{code}
}

\begin{code}
mutual
  ⟦_⟧poly : {Δ : ClockCtx} → Poly Δ → SemPoly Δ
  ⟦_⟧poly (∁ A) = ∁ ⟦ A ⟧A
  ⟦ I ⟧poly = I
  ⟦ P ⊞ Q ⟧poly = ⟦ P ⟧poly ⊞ ⟦ Q ⟧poly
  ⟦ P ⊠ Q ⟧poly = ⟦ P ⟧poly ⊠ ⟦ Q ⟧poly
  ⟦ ▻ P ⟧poly = ▸ ⟦ P ⟧poly

  ⟦_⟧A : {Δ : ClockCtx} → Ty Δ → SemTy Δ
  ⟦ 𝟙 ⟧A = Unit
  ⟦ A ⊞ B ⟧A = ⟦ A ⟧A ⊕ ⟦ B ⟧A
  ⟦ A ⊠ B ⟧A = ⟦ A ⟧A ⊗ ⟦ B ⟧A
  ⟦ A ⟶ B ⟧A = ⟦ A ⟧A ⇒ ⟦ B ⟧A
  ⟦ ⇡ A ⟧A = ⇑ ⟦ A ⟧A
  ⟦ ▻ A ⟧A = ►(⟦ A ⟧A)
  ⟦ □ A ⟧A = ■(⟦ A ⟧A)
  ⟦ μ P ⟧A = mu ⟦ P ⟧poly  
  
⟦_⟧Γ : {Δ : ClockCtx} → Ctx Δ → SemCtx Δ
⟦ • ⟧Γ = ∙ _
⟦ Γ , A ⟧Γ = (⟦ Γ ⟧Γ) ,, ⟦ A ⟧A
⟦ ⇡ Γ ⟧Γ = ⇑ ⟦ Γ ⟧Γ

consset' : (P Q : Poly ∅) → ⟦ eval Q (μ P) ⟧A → μset ⟦ P ⟧poly ⟦ Q ⟧poly
consset' P (∁ x) t = ∁s t -- ∁s t
consset' P I t = I t -- I t
consset' P (Q ⊞ Q₁) (inj₁ x) = ⊞₁ (consset' P Q x)
consset' P (Q ⊞ Q₁) (inj₂ y) = ⊞₂ (consset' P Q₁ y)
consset' P (Q₁ ⊠ Q₂) t = consset' P Q₁ (proj₁ t) ⊠ consset' P Q₂ (proj₂ t)

cons₁' : (P Q : Poly κ) (i : Size) → Obj ⟦ eval Q (μ P) ⟧A i → μObj' ⟦ P ⟧poly ⟦ Q ⟧poly i
cons₂' : (P Q : Poly κ) (i : Size) (j : Size< (↑ i)) (t : Obj ⟦ eval Q (μ P) ⟧A i)
  → μMor' ⟦ P ⟧poly ⟦ Q ⟧poly i j (cons₁' P Q i t) ≡ cons₁' P Q j (Mor ⟦ eval Q (μ P) ⟧A i j t)
cons₁' P (∁ X) i t = const t
cons₁' P I i t = rec t
cons₁' P (Q ⊠ R) i (t , u) = (cons₁' P Q i t) , (cons₁' P R i u)
cons₁' P (Q ⊞ R) i (inj₁ t) = in₁ (cons₁' P Q i t)
cons₁' P (Q ⊞ R) i (inj₂ t) = in₂ (cons₁' P R i t)
cons₁' P (▻ Q) i t = later c₁ c₂
  where
    c₁ : Later (μObj' ⟦ P ⟧poly ⟦ Q ⟧poly) i
    c₁ [ j ] = cons₁' P Q j (►cone t [ j ])
    c₂ : LaterLim (μObj' ⟦ P ⟧poly ⟦ Q ⟧poly) (μMor' ⟦ P ⟧poly ⟦ Q ⟧poly) i c₁
    c₂ [ j ] [ k ] = trans (cons₂' P Q j k (►cone t [ j ])) (cong (cons₁' P Q k) (►com t [ j ] [ k ]))
cons₂' P (∁ X) i j t = refl
cons₂' P I i j t = refl
cons₂' P (Q ⊠ R) i j (t , u) = cong₂ _,_ (cons₂' P Q i j t) (cons₂' P R i j u)
cons₂' P (Q ⊞ R) i j (inj₁ t) = cong in₁ (cons₂' P Q i j t)
cons₂' P (Q ⊞ R) i j (inj₂ t) = cong in₂ (cons₂' P R i j t)
cons₂' P (▻ Q) i j t =
  cong₂-dep later (funext (λ { [ _ ] → refl})) (funext (λ { [ _ ] → funext (λ { [ _ ] → uip }) }))

conspsh : (P Q : Poly κ) (Γ : Ctx κ) → SemTm ⟦ Γ ⟧Γ ⟦ eval Q (μ P) ⟧A → SemTm ⟦ Γ ⟧Γ (μ-κ ⟦ P ⟧poly ⟦ Q ⟧poly)
nat-map (conspsh P Q Γ t) i γ  = cons₁' P Q i (nat-map t i γ)
nat-com (conspsh P Q Γ t) i j γ = trans (cons₂' P Q i j (nat-map t i γ)) (cong (cons₁' P Q j) (nat-com t i j γ))

primrec-set' : (P Q : Poly ∅) (A : Ty ∅)
  → ⟦ eval P (μ P ⊠ A) ⟶ A ⟧A
  → (μset ⟦ P ⟧poly ⟦ Q ⟧poly)
  → ⟦ eval Q (μ P ⊠ A) ⟧A
primrec-set' P (∁ X) A y (∁s z) = z
primrec-set' P I A y (I z) = z , y (primrec-set' P P A y z)
primrec-set' P (Q₁ ⊞ Q₂) A y (⊞₁ z) = inj₁ (primrec-set' P Q₁ A y z)
primrec-set' P (Q₁ ⊞ Q₂) A y (⊞₂ z) = inj₂ (primrec-set' P Q₂ A y z)
proj₁ (primrec-set' P (Q₁ ⊠ Q₂) A y (z₁ ⊠ z₂)) = primrec-set' P Q₁ A y z₁
proj₂ (primrec-set' P (Q₁ ⊠ Q₂) A y (z₁ ⊠ z₂)) = primrec-set' P Q₂ A y z₂

primrec-set : (P : Poly ∅) (Γ : Ctx ∅) (A : Ty ∅)
  → SemTm ⟦ Γ ⟧Γ ⟦ eval P (μ P ⊠ A) ⟶ A ⟧A
  → SemTm ⟦ Γ ⟧Γ (mu ⟦ P ⟧poly ⇒ ⟦ A ⟧A)
primrec-set P Γ A t x a = t x (primrec-set' P P A (t x) a)

primrec-psh'₁₁ : (P Q : Poly κ) (A : Ty κ) (i : Size) (t : Obj ⟦ eval P (μ P ⊠ A) ⟶ A ⟧A i)
  → (j : Size< (↑ i)) (z : μObj' ⟦ P ⟧poly ⟦ Q ⟧poly j)
  → Obj ⟦ eval Q (μ P ⊠ A) ⟧A j
primrec-psh'₁₂ : (P Q : Poly κ) (A : Ty κ) (i : Size) (t : Obj ⟦ eval P (μ P ⊠ A) ⟶ A ⟧A i)
  → (j : Size< (↑ i)) (z : μObj' ⟦ P ⟧poly ⟦ Q ⟧poly j) (k : Size< (↑ j))
  → Mor ⟦ eval Q (μ P ⊠ A) ⟧A j k (primrec-psh'₁₁ P Q A i t j z)
    ≡
    primrec-psh'₁₁ P Q A i t k (μMor' ⟦ P ⟧poly ⟦ Q ⟧poly j k z)
primrec-psh'₁₁ P (∁ X) A i t j (const z) = z
primrec-psh'₁₁ P I A i t j (rec z) = (z , fun t j (primrec-psh'₁₁ P P A i t j z))
primrec-psh'₁₁ P (Q₁ ⊞ Q₂) A i t j (in₁ z) = inj₁ (primrec-psh'₁₁ P Q₁ A i t j z)
primrec-psh'₁₁ P (Q₁ ⊞ Q₂) A i t j (in₂ z) = inj₂ (primrec-psh'₁₁ P Q₂ A i t j z)
proj₁ (primrec-psh'₁₁ P (Q₁ ⊠ Q₂) A i t j (z₁ , z₂)) = primrec-psh'₁₁ P Q₁ A i t j z₁
proj₂ (primrec-psh'₁₁ P (Q₁ ⊠ Q₂) A i t j (z₁ , z₂)) = primrec-psh'₁₁ P Q₂ A i t j z₂
►cone (primrec-psh'₁₁ P (▻ Q) A i t j (later z₁ z₂)) [ k ] = primrec-psh'₁₁ P Q A i t k (z₁ [ k ]) 
►com (primrec-psh'₁₁ P (▻ Q) A i t j (later z₁ z₂)) [ k ] [ l ] = 
  trans (primrec-psh'₁₂ P Q A i t k (z₁ [ k ]) l)
        (cong (primrec-psh'₁₁ P Q A i t l) (z₂ [ k ] [ l ]))
primrec-psh'₁₂ P (∁ X) A i t j (const z) k = refl
primrec-psh'₁₂ P I A i f j (rec z) k =
  cong (λ z → (_ , z))
       (trans (funcom f j k (primrec-psh'₁₁ P P A i f j z))
              ((cong (fun f k) (primrec-psh'₁₂ P P A i f j z k))))
primrec-psh'₁₂ P (Q₁ ⊞ Q₂) A i t j (in₁ z) k = cong inj₁ (primrec-psh'₁₂ P Q₁ A i t j z k)
primrec-psh'₁₂ P (Q₁ ⊞ Q₂) A i t j (in₂ z) k = cong inj₂ (primrec-psh'₁₂ P Q₂ A i t j z k)
primrec-psh'₁₂ P (Q₁ ⊠ Q₂) A i t j (z₁ , z₂) k = 
  cong₂ (_,_) (primrec-psh'₁₂ P Q₁ A i t j z₁ k) (primrec-psh'₁₂ P Q₂ A i t j z₂ k)
primrec-psh'₁₂ P (▻ Q) A i t j (later z₁ z₂) k = ►eq (λ {_ → refl})

primrec-psh'₂ : (P Q : Poly κ) (Γ : SemCtx κ) (A : Ty κ) (t : SemTm Γ ⟦ eval P (μ P ⊠ A) ⟶ A ⟧A)
  → (i : Size) (j : Size< (↑ i)) (x : Obj Γ i) (k : Size< (↑ j)) (z : μObj' ⟦ P ⟧poly ⟦ Q ⟧poly k)
  → primrec-psh'₁₁ P Q A i (nat-map t i x) k z
    ≡
    primrec-psh'₁₁ P Q A j (nat-map t j (Mor Γ i j x)) k z
primrec-psh'₂ P (∁ X) Γ A t i j x k (const z) = refl
primrec-psh'₂ P I Γ A t i j x k (rec z) =
  cong (λ q → (z , q))
       (trans (cong (λ q → fun q k (primrec-psh'₁₁ P P A i (nat-map t i x) k z)) (nat-com t i j x))
              (cong (λ z → fun (nat-map t j (Mor Γ i j x)) k z) (primrec-psh'₂ P P Γ A t i j x k z)))
primrec-psh'₂ P (Q₁ ⊞ Q₂) Γ A t i j x k (in₁ z) = cong inj₁ (primrec-psh'₂ P Q₁ Γ A t i j x k z)
primrec-psh'₂ P (Q₁ ⊞ Q₂) Γ A t i j x k (in₂ z) = cong inj₂ (primrec-psh'₂ P Q₂ Γ A t i j x k z)
primrec-psh'₂ P (Q₁ ⊠ Q₂) Γ A t i j x k (z₁ , z₂) =
  cong₂ (_,_) (primrec-psh'₂ P Q₁ Γ A t i j x k z₁) (primrec-psh'₂ P Q₂ Γ A t i j x k z₂)
primrec-psh'₂ P (▻ Q) Γ A t i j x k (later z₁ z₂) =
  ►eq (λ {l → primrec-psh'₂ P Q Γ A t i j x l (z₁ [ l ])})

primrec-psh : (P : Poly κ) (Γ : Ctx κ) (A : Ty κ)
  → SemTm ⟦ Γ ⟧Γ ⟦ eval P (μ P ⊠ A) ⟶ A ⟧A
  → SemTm ⟦ Γ ⟧Γ (mu ⟦ P ⟧poly ⇒ ⟦ A ⟧A)
fun (nat-map (primrec-psh P Γ A f) i x) j y = fun (nat-map f i x) j (primrec-psh'₁₁ P P A i (nat-map f i x) j y)
funcom (nat-map (primrec-psh P Γ A f) i x) j k y =
  trans (funcom (nat-map f i x) j k _)
        (cong (fun (nat-map f i x) k) (primrec-psh'₁₂ P P A i (nat-map f i x) j y k))
nat-com (primrec-psh P Γ A t) i j x = funeq (λ k z → cong₂ (λ a b → fun a k b) (nat-com t i j x) (primrec-psh'₂ P P ⟦ Γ ⟧Γ A t i j x k z))

{-
primrec-psh'₁₁ : (P Q : Poly κ) (A : Type κ) (i : Size) (t : Obj ⟦ (eval P (μ P) ⊠ eval P A) ⟶ A ⟧A i)
  → (j : Size< (↑ i)) (z : μObj' ⟦ P ⟧poly ⟦ Q ⟧poly j)
  → Obj ⟦ eval Q (μ P) ⊠ eval Q A ⟧A j
primrec-psh'₁₂ : (P Q : Poly κ) (A : Type κ) (i : Size) (t : Obj ⟦ (eval P (μ P) ⊠ eval P A) ⟶ A ⟧A i)
  → (j : Size< (↑ i)) (z : μObj' ⟦ P ⟧poly ⟦ Q ⟧poly j) (k : Size< (↑ j))
  → Mor ⟦ eval Q (μ P) ⊠ eval Q A ⟧A j k (primrec-psh'₁₁ P Q A i t j z)
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

primrec-psh'₂ : (P Q : Poly κ) (Γ : Ctx κ) (A : Type κ) (t : Tm Γ ⟦ (eval P (μ P) ⊠ eval P A) ⟶ A ⟧A)
  → (i : Size) (j : Size< (↑ i)) (x : Obj Γ i) (k : Size< (↑ j)) (z : μObj' ⟦ P ⟧poly ⟦ Q ⟧poly k)
  → primrec-psh'₁₁ P Q A i (nat-map t i x) k z
    ≡
    primrec-psh'₁₁ P Q A j (nat-map t j (Mor Γ i j x)) k z
primrec-psh'₂ P (∁ X) Γ A t i j x k (∁ps z) = refl
primrec-psh'₂ P I Γ A t i j x k (I z) =
  cong (λ q → (z , q))
       (trans (cong (λ q → fun q k (primrec-psh'₁₁ P P A i (nat-map t i x) k z)) (nat-com t i j x))
              (cong (λ z → fun (nat-map t j (Mor Γ i j x)) k z) (primrec-psh'₂ P P Γ A t i j x k z)))
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

primrec-psh : (P : Poly κ) (Γ : Ctx κ) (A : Type κ)
  → Tm ⟦ Γ ⟧Γ ⟦ (eval P (μ P) ⊠ eval P A) ⟶ A ⟧A
  → Tm ⟦ Γ ⟧Γ (mu ⟦ P ⟧poly ⇒ ⟦ A ⟧A)
fun (nat-map (primrec-psh P Γ A f) i x) j y = fun (nat-map f i x) j (primrec-psh'₁₁ P P A i (nat-map f i x) j y)
funcom (nat-map (primrec-psh P Γ A f) i x) j k y =
  trans (funcom (nat-map f i x) j k _)
        (cong (fun (nat-map f i x) k) (primrec-psh'₁₂ P P A i (nat-map f i x) j y k))
nat-com (primrec-psh P Γ A t) i j x = funeq (λ k z → cong₂ (λ a b → fun a k b) (nat-com t i j x) (primrec-psh'₂ P P ⟦ Γ ⟧Γ A t i j x k z))
-}

μweaken-help : (P Q : Poly ∅) → μset ⟦ P ⟧poly ⟦ Q ⟧poly → (i : Size) → μObj' ⟦ weakenP P ⟧poly ⟦ weakenP Q ⟧poly i
μweaken-help P (∁ X) (∁s x) i = const x
μweaken-help P I (I x) i = rec (μweaken-help P P x i)
μweaken-help P (Q₁ ⊞ Q₂) (⊞₁ x) i = in₁ (μweaken-help P Q₁ x i)
μweaken-help P (Q₁ ⊞ Q₂) (⊞₂ x) i = in₂ (μweaken-help P Q₂ x i)
μweaken-help P (Q₁ ⊠ Q₂) (x₁ ⊠ x₂) i = μweaken-help P Q₁ x₁ i , μweaken-help P Q₂ x₂ i

μweaken-eq : (P Q : Poly ∅) (x : μset ⟦ P ⟧poly ⟦ Q ⟧poly) (i : Size) (j : Size< (↑ i)) (k : Size< (↑ j))
  → μMor' ⟦ weakenP P ⟧poly ⟦ weakenP Q ⟧poly j k
          (μweaken-help P Q x j)
    ≡
    μweaken-help P Q x k
μweaken-eq P (∁ X) (∁s x) i j k = refl
μweaken-eq P I (I x) i j k = cong rec (μweaken-eq P P x i j k)
μweaken-eq P (Q₁ ⊞ Q₂) (⊞₁ x) i j k = cong in₁ (μweaken-eq P Q₁ x i j k)
μweaken-eq P (Q₁ ⊞ Q₂) (⊞₂ x) i j k = cong in₂ (μweaken-eq P Q₂ x i j k)
μweaken-eq P (Q₁ ⊠ Q₂) (x₁ ⊠ x₂) i j k =
  cong₂ _,_ (μweaken-eq P Q₁ x₁ i j k) (μweaken-eq P Q₂ x₂ i j k)

weakenμ-help : (P Q : Poly ∅) → (i : Size) → μObj' ⟦ weakenP P ⟧poly ⟦ weakenP Q ⟧poly i → μset ⟦ P ⟧poly ⟦ Q ⟧poly
weakenμ-help P (∁ X) i (const x) = ∁s x
weakenμ-help P I i (rec x) = I (weakenμ-help P P i x)
weakenμ-help P (Q₁ ⊞ Q₂) i (in₁ x) = ⊞₁ (weakenμ-help P Q₁ i x)
weakenμ-help P (Q₁ ⊞ Q₂) i (in₂ x) = ⊞₂ (weakenμ-help P Q₂ i x)
weakenμ-help P (Q₁ ⊠ Q₂) i (x₁ , x₂) = weakenμ-help P Q₁ i x₁ ⊠ weakenμ-help P Q₂ i x₂

weakenμ-eq : (P Q : Poly ∅) (i : Size) (x : μObj' ⟦ weakenP P ⟧poly ⟦ weakenP Q ⟧poly i) (j : Size< (↑ i))
  → weakenμ-help P Q i x
    ≡
    weakenμ-help P Q j (μMor' ⟦ weakenP P ⟧poly ⟦ weakenP Q ⟧poly i j x)
weakenμ-eq P (∁ X) i (const x) j = refl
weakenμ-eq P I i (rec x) j = cong I (weakenμ-eq P P i x j)
weakenμ-eq P (Q₁ ⊞ Q₂) i (in₁ x) j = cong ⊞₁ (weakenμ-eq P Q₁ i x j)
weakenμ-eq P (Q₁ ⊞ Q₂) i (in₂ x) j = cong ⊞₂ (weakenμ-eq P Q₂ i x j)
weakenμ-eq P (Q₁ ⊠ Q₂) i (x₁ , x₂) j =
  cong₂ (_⊠_) (weakenμ-eq P Q₁ i x₁ j) (weakenμ-eq P Q₂ i x₂ j)

mutual
  ⟦_⟧sub : {Δ : ClockCtx} {Γ Γ' : Ctx Δ} → Sub Γ Γ' → SemSub ⟦ Γ ⟧Γ ⟦ Γ' ⟧Γ
  ⟦ ε Γ ⟧sub = sem-ε ⟦ Γ ⟧Γ
  ⟦ id Γ ⟧sub = sem-idsub ⟦ Γ ⟧Γ
  ⟦ s , x ⟧sub = sem-subst-tm _ _ _ ⟦ s ⟧sub ⟦ x ⟧tm
  ⟦ s ∘ s' ⟧sub = sem-subcomp _ _ _ ⟦ s ⟧sub ⟦ s' ⟧sub
  ⟦ pr {_} {Γ} {Γ'} {A} s ⟧sub = sem-subpr ⟦ Γ ⟧Γ ⟦ Γ' ⟧Γ ⟦ A ⟧A ⟦ s ⟧sub
  ⟦ down s ⟧sub = nat-map ⟦ s ⟧sub ∞ 
  nat-map ⟦ up s ⟧sub i = ⟦ s ⟧sub
  nat-com ⟦ up s ⟧sub i j x = refl
  nat-map ⟦ •⇡ ⟧sub i tt = tt
  nat-com ⟦ •⇡ ⟧sub i j x = refl
  nat-map ⟦ ,⇡ Γ A ⟧sub i x = x
  nat-com ⟦ ,⇡ Γ A ⟧sub i j x = refl
  
  ⟦_⟧tm : {Δ : ClockCtx} {Γ : Ctx Δ} {A : Ty Δ} → Tm Γ A → SemTm ⟦ Γ ⟧Γ ⟦ A ⟧A
  ⟦ sub t s ⟧tm = sem-sub _ _ _ ⟦ t ⟧tm ⟦ s ⟧sub
  ⟦ var Γ A ⟧tm = sem-var ⟦ Γ ⟧Γ ⟦ A ⟧A
  ⟦ tt ⟧tm = ⋆ _
  ⟦ unit-rec t ⟧tm = Unit-rec _ _ ⟦ t ⟧tm
  ⟦ in₁ B t ⟧tm = inl _ _ ⟦ B ⟧A ⟦ t ⟧tm
  ⟦ in₂ A t ⟧tm = inr _ ⟦ A ⟧A _ ⟦ t ⟧tm
  ⟦ ⊞rec C l r ⟧tm = sum-rec _ _ _ ⟦ C ⟧A ⟦ l ⟧tm ⟦ r ⟧tm
  ⟦ [ t₁ & t₂ ] ⟧tm = pair _ _ _ ⟦ t₁ ⟧tm ⟦ t₂ ⟧tm
  ⟦ π₁ t ⟧tm = pr₁ _ _ _ ⟦ t ⟧tm
  ⟦ π₂ t ⟧tm = pr₂ _ _ _ ⟦ t ⟧tm
  ⟦ lambda t ⟧tm = sem-lambda _ _ _ ⟦ t ⟧tm
  ⟦ app f ⟧tm = sem-app _ _ _ ⟦ f ⟧tm
  ⟦ up t ⟧tm = sem-up _ _ ⟦ t ⟧tm
  ⟦ down t ⟧tm = sem-down _ _ ⟦ t ⟧tm
  ⟦ box {Γ} {A} t ⟧tm = sem-box ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ t ⟧tm
  ⟦ unbox {Γ} {A} t ⟧tm = sem-unbox ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ t ⟧tm
  ⟦ next {Γ} {A} t ⟧tm = sem-next ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ t ⟧tm
  ⟦ _⊛_ {Γ} {A} {B} f t ⟧tm = fmap ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ B ⟧A ⟦ f ⟧tm ⟦ t ⟧tm
  ⟦ dfix {Γ} {A} f ⟧tm = sem-dfix ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ f ⟧tm
  ⟦ force {Γ} {A} t ⟧tm = sem-force ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ t ⟧tm
  ⟦_⟧tm {∅} {Γ} (cons P t) z = consset' P P (⟦ t ⟧tm z)
  ⟦_⟧tm {κ} {Γ} (cons P t) = conspsh P P Γ ⟦ t ⟧tm
  ⟦_⟧tm {∅} (primrec P {Γ} {A} t) = primrec-set P Γ A ⟦ t ⟧tm
  ⟦_⟧tm {κ} (primrec P {Γ} {A} t) = primrec-psh P Γ A ⟦ t ⟧tm 
  ⟦ □const A ⟧tm = ■const-tm _ ⟦ A ⟧A
  ⟦ □sum A B ⟧tm = ■sum-tm _ ⟦ A ⟧A ⟦ B ⟧A
  fun (nat-map ⟦ ⟶weaken A B ⟧tm i x) j f = fun f j
  funcom (nat-map ⟦ ⟶weaken A B ⟧tm i x) j k f = funext (funcom f j k) 
  nat-com ⟦ ⟶weaken A B ⟧tm i j x = funeq (λ _ _ → refl)
  fun (nat-map ⟦ μweaken P ⟧tm i x) j y = μweaken-help P P y j
  funcom (nat-map ⟦ μweaken P ⟧tm i x) j k y = μweaken-eq P P y i j k
  nat-com ⟦ μweaken P ⟧tm i j x = funeq (λ _ _ → refl)
  fun (nat-map ⟦ weakenμ P ⟧tm i x) j y = weakenμ-help P P j y
  funcom (nat-map ⟦ weakenμ P ⟧tm i x) j k y = weakenμ-eq P P j y k
  nat-com ⟦ weakenμ P ⟧tm i j x = funeq (λ _ _ → refl)
\end{code}
