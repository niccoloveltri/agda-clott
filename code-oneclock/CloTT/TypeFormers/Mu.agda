module CloTT.TypeFormers.Mu where

open import Data.Sum renaming (map to map⊎)
open import Data.Product renaming (map to map×)
open import Prelude
open import Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers

data Poly : Set₁ where
  I : Poly
  _⊞_ _⊠_ : Poly → Poly → Poly
  ► : Poly → Poly
  ∁ : Set → Poly

mutual 
  data MuObj (P : Poly) : Poly → Size → Set where
    supI : ∀ {i} → MuObj P P i → MuObj P I i
    sup⊠ : ∀ {Q₁ Q₂ i} → MuObj P Q₁ i → MuObj P Q₂ i → MuObj P (Q₁ ⊠ Q₂) i
    sup⊞₁ : ∀ {Q₁ Q₂ i} → MuObj P Q₁ i → MuObj P (Q₁ ⊞ Q₂) i
    sup⊞₂ : ∀ {Q₁ Q₂ i} → MuObj P Q₂ i → MuObj P (Q₁ ⊞ Q₂) i
    sup► : ∀ {Q i} → (t : Later (MuObj P Q) i)
      → ((j : Size< i) (k : Size≤ j) → MuMor P Q j k (t [ j ]) ≡ t [ k ])
      → MuObj P (► Q) i
    sup∁ : ∀ {X i} → X → MuObj P (∁ X) i

  MuMor : (P Q : Poly) (i : Size) (j : Size≤ i) → MuObj P Q i → MuObj P Q j
  MuMor P I i j (supI t) = supI (MuMor P P i j t)
  MuMor P (Q₁ ⊠ Q₂) i j (sup⊠ t u) = sup⊠ (MuMor P Q₁ i j t) (MuMor P Q₂ i j u)
  MuMor P (Q₁ ⊞ Q₂) i j (sup⊞₁ t) = sup⊞₁ (MuMor P Q₁ i j t)
  MuMor P (Q₁ ⊞ Q₂) i j (sup⊞₂ t) = sup⊞₂ (MuMor P Q₂ i j t)
  MuMor P (► Q) i j (sup► t p) = sup► t p
  MuMor P (∁ X) i j (sup∁ x) = sup∁ x


MuMorId : (P Q : Poly) {i : Size} {x : MuObj P Q i} → MuMor P Q i i x ≡ x
MuMorId P I {_} {supI t} = cong supI (MuMorId P P)
MuMorId P (Q₁ ⊠ Q₂) {_} {sup⊠ t u} = cong₂ sup⊠ (MuMorId P Q₁) (MuMorId P Q₂)
MuMorId P (Q₁ ⊞ Q₂) {_} {sup⊞₁ t} = cong sup⊞₁ (MuMorId P Q₁)
MuMorId P (Q₁ ⊞ Q₂) {_} {sup⊞₂ t} = cong sup⊞₂ (MuMorId P Q₂)
MuMorId P (► Q) {_} {sup► t p} = refl
MuMorId P (∁ X) {_} {sup∁ x} = refl

MuMorComp : (P Q : Poly) {i : Size} {j : Size≤ i} {k : Size≤ j} {x : MuObj P Q i}
  → MuMor P Q i k x ≡ MuMor P Q j k (MuMor P Q i j x)
MuMorComp P I {_} {_} {_} {supI t} = cong supI (MuMorComp P P)
MuMorComp P (Q₁ ⊠ Q₂) {_} {_} {_} {sup⊠ t u} = cong₂ sup⊠ (MuMorComp P Q₁) (MuMorComp P Q₂)
MuMorComp P (Q₁ ⊞ Q₂) {_} {_} {_} {sup⊞₁ t} = cong sup⊞₁ (MuMorComp P Q₁)
MuMorComp P (Q₁ ⊞ Q₂) {_} {_} {_} {sup⊞₂ t} = cong sup⊞₂ (MuMorComp P Q₂)
MuMorComp P (► Q) {_} {_} {_} {sup► t p} = refl
MuMorComp P (∁ X) {_} {_} {_} {sup∁ x} = refl

Mu : Poly → PSh
Mu P = record
  { Obj = MuObj P P
  ; Mor = MuMor P P
  ; MorId = MuMorId P P
  ; MorComp = MuMorComp P P
  }

eval : (P : Poly) → PSh → PSh
eval I A = A
eval (P ⊞ Q) A = Sum (eval P A) (eval Q A)
eval (P ⊠ Q) A = Prod (eval P A) (eval Q A)
eval (► P) A = ▻ (eval P A)
eval (∁ Q) A = WC Q

μ : Poly → Ty tot
μ = Mu

sup►-eq : {P Q : Poly} {i : Size} {t u : Later (MuObj P Q) i}
  → ∀ {p q} → u ≡ t → sup► u p ≡ sup► t q
sup►-eq refl = cong (sup► _) (funext (λ { _ → funext (λ _ → uip)}))

mutual 
  cons₁ : (P Q : Poly) (i : Size) → PSh.Obj (eval Q (μ P)) i → MuObj P Q i
  cons₁ P I i t = supI t
  cons₁ P (Q₁ ⊞ Q₂) i (inj₁ t) = sup⊞₁ (cons₁ P Q₁ i t)
  cons₁ P (Q₁ ⊞ Q₂) i (inj₂ t) = sup⊞₂ (cons₁ P Q₂ i t)
  cons₁ P (Q₁ ⊠ Q₂) i (t₁ , t₂) = sup⊠ (cons₁ P Q₁ i t₁) (cons₁ P Q₂ i t₂)
  cons₁ P (► Q) i (t , p) =
    sup► (λ { [ j ] → cons₁ P Q j (t [ j ]) })
         (λ { j k →  trans (cons₂ P Q j k (t [ j ])) (cong (cons₁ P Q k) (p j k))})
  cons₁ P (∁ X) i t = sup∁ t

  cons₂ : (P Q : Poly) (i : Size) (j : Size≤ i) (t : PSh.Obj (eval Q (μ P)) i)
    → MuMor P Q i j (cons₁ P Q i t) ≡ cons₁ P Q j (PSh.Mor (eval Q (μ P)) i j t)
  cons₂ P I i j t = refl
  cons₂ P (Q₁ ⊞ Q₂) i j (inj₁ t) = cong sup⊞₁ (cons₂ P Q₁ i j t)
  cons₂ P (Q₁ ⊞ Q₂) i j (inj₂ t) = cong sup⊞₂ (cons₂ P Q₂ i j t)
  cons₂ P (Q₁ ⊠ Q₂) i j (t₁ , t₂) = cong₂ sup⊠ (cons₂ P Q₁ i j t₁) (cons₂ P Q₂ i j t₂)
  cons₂ P (► Q) i j (t , p) = sup►-eq (funext (λ { [ k ] → refl }))
  cons₂ P (∁ X) i j t = refl

cons : (P : Poly) (Γ : Ctx tot) → Tm tot Γ (eval P (μ P)) → Tm tot Γ (μ P)
proj₁ (cons P Γ (t , p)) i γ = cons₁ P P i (t i γ)
proj₂ (cons P Γ (t , p)) i j γ =
  begin
    MuMor P P i j (cons₁ P P i (t i γ))
  ≡⟨ cons₂ P P i j (t i γ) ⟩
    cons₁ P P j (PSh.Mor (eval P (Mu P)) i j (t i γ))
  ≡⟨ cong (cons₁ P P j) (p i j γ) ⟩
    cons₁ P P j (t j (PSh.Mor Γ i j γ))
  ∎

▻Obj-eq : {A : Ty tot} {i : Size} {t u : Later (PSh.Obj A) i}
  → ∀{p q} → t ≡ u → _≡_ {A = ▻Obj A i} (t , p) (u , q)
▻Obj-eq r = Σ≡-uip (funext (λ { _ → funext (λ _ → uip) })) r

mutual
  cons-inv₁ : (P Q : Poly) (i : Size) → MuObj P Q i → PSh.Obj (eval Q (Mu P)) i
  cons-inv₁ P I i (supI t) = t
  cons-inv₁ P (Q₁ ⊞ Q₂) i (sup⊞₁ t) = inj₁ (cons-inv₁ P Q₁ i t)
  cons-inv₁ P (Q₁ ⊞ Q₂) i (sup⊞₂ t) = inj₂ (cons-inv₁ P Q₂ i t)
  cons-inv₁ P (Q₁ ⊠ Q₂) i (sup⊠ t₁ t₂) = cons-inv₁ P Q₁ i t₁ , cons-inv₁ P Q₂ i t₂
  cons-inv₁ P (► Q) i (sup► t p) =
    (λ { [ j ] → cons-inv₁ P Q j (t [ j ]) }) ,
    (λ { j k → trans (cons-inv₂ P Q j k (t [ j ])) (cong (cons-inv₁ P Q k) (p j k)) })
  cons-inv₁ P (∁ X) i (sup∁ x) = x

  cons-inv₂ : (P Q : Poly) (i : Size) (j : Size≤ i) (t : MuObj P Q i) 
    → PSh.Mor (eval Q (Mu P)) i j (cons-inv₁ P Q i t) ≡ cons-inv₁ P Q j (MuMor P Q i j t)
  cons-inv₂ P I i j (supI t) = refl
  cons-inv₂ P (Q₁ ⊞ Q₂) i j (sup⊞₁ t) = cong inj₁ (cons-inv₂ P Q₁ i j t)
  cons-inv₂ P (Q₁ ⊞ Q₂) i j (sup⊞₂ t) = cong inj₂ (cons-inv₂ P Q₂ i j t)
  cons-inv₂ P (Q₁ ⊠ Q₂) i j (sup⊠ t₁ t₂) = cong₂ _,_ (cons-inv₂ P Q₁ i j t₁) (cons-inv₂ P Q₂ i j t₂)
  cons-inv₂ P (► Q) i j (sup► t p) = ▻Obj-eq {eval Q (Mu P)} (funext (λ { [ j ] → refl }))
  cons-inv₂ P (∁ X) i j (sup∁ x) = refl

  primrec₁₁'' : (P Q : Poly) (A : Ty tot) (i : Size)
    → ((j : Size≤ i) → PSh.Obj (eval Q (Prod (Mu P) A)) j → PSh.Obj A j)
    → (j : Size≤ i) → PSh.Obj (eval Q (Prod (Mu P) A)) j → PSh.Obj A j
--    → (j : Size≤ i) → MuObj P Q j → PSh.Obj (eval Q (Prod (Mu P) A)) j    
  primrec₁₁'' P I A i f j (t , x) = x
  primrec₁₁'' P (Q ⊞ Q₁) A i f j (inj₁ x) = {!!}
  primrec₁₁'' P (Q ⊞ Q₁) A i f j (inj₂ y) = {!!}
  primrec₁₁'' P (Q ⊠ Q₁) A i f j t = {!!}
  primrec₁₁'' P (► Q) A i f j t = {!!}
  primrec₁₁'' P (∁ x) A i f j t = {!!}

  primrec₁₁' : (P Q : Poly) (A : Ty tot) (i : Size)
    → ((j : Size≤ i) → PSh.Obj (eval Q (Prod (Mu P) A)) j → PSh.Obj A j)
    → (j : Size≤ i) → MuObj P Q j → PSh.Obj (eval Q (Prod (Mu P) A)) j
  primrec₁₁' P I A i f j (supI t) = t , {!!} --primrec₁₁'' P P A i (λ k x → {!f!}) j (primrec₁₁' P P A i {!!} j t)
  primrec₁₁' P (Q ⊞ Q₁) A i f j t = {!!}
  primrec₁₁' P (Q ⊠ Q₁) A i f j t = {!!}
  primrec₁₁' P (► Q) A i f j t = {!!}
  primrec₁₁' P (∁ x) A i f j t = {!!}
{-    
  primrec₁₁' P I A i t j (supI x) = {!!}
  primrec₁₁' P (Q₁ ⊞ Q₂) A i t j (sup⊞₁ x) = {!!}
  primrec₁₁' P (Q₁ ⊞ Q₂) A i t j (sup⊞₂ x) = {!!} --primrec₁₁ P Q₂ A i (λ j y → t j (inj₂ y)) j x
  primrec₁₁' P (Q₁ ⊠ Q₂) A i t j (sup⊠ x₁ x₂) = t j ({!!} , {!!})
  primrec₁₁' P (► Q) A i t = {!!}
  primrec₁₁' P (∁ X) A i t j (sup∁ x) = t j x
-}

{-
mutual
  eval-fst : (P : Poly) (A B : PSh) (i : Size)
    → PSh.Obj (eval P (Prod A B)) i → PSh.Obj (eval P A) i × PSh.Obj (eval P B) i
  eval-fst I A B i t = t
  proj₁ (eval-fst (P ⊞ P₁) A B i (inj₁ x)) = inj₁ (proj₁ (eval-fst P A B i x))
  proj₂ (eval-fst (P ⊞ P₁) A B i (inj₁ x)) = inj₁ (proj₂ (eval-fst P A B i x))
  proj₁ (eval-fst (P ⊞ P₁) A B i (inj₂ y)) = inj₂ (proj₁ (eval-fst P₁ A B i y))
  proj₂ (eval-fst (P ⊞ P₁) A B i (inj₂ y)) = inj₂ (proj₂ (eval-fst P₁ A B i y))
  proj₁ (proj₁ (eval-fst (P ⊠ P₁) A B i (x , y))) = proj₁ (eval-fst P A B i x) 
  proj₂ (proj₁ (eval-fst (P ⊠ P₁) A B i (x , y))) = proj₁ (eval-fst P₁ A B i y)  
  proj₁ (proj₂ (eval-fst (P ⊠ P₁) A B i (x , y))) = proj₂ (eval-fst P A B i x)  
  proj₂ (proj₂ (eval-fst (P ⊠ P₁) A B i (x , y))) = proj₂ (eval-fst P₁ A B i y)  
  proj₁ (proj₁ (eval-fst (► P) A B i (t , p))) [ j ] = proj₁ (eval-fst P A B j (t [ j ]))
  proj₂ (proj₁ (eval-fst (► P) A B i (t , p))) j k = {!!}
  proj₁ (proj₂ (eval-fst (► P) A B i (t , p))) [ j ] = proj₂ (eval-fst P A B j (t [ j ]))
  proj₂ (proj₂ (eval-fst (► P) A B i (t , p))) j k = {!!}
  eval-fst (∁ X) A B i t = t , t

  eval-lax' : (P : Poly) (A B : PSh) (i : Size) (j : Size≤ i)
    → PSh.Mor (eval P A) j k (proj₁ (eval-lax P A B j (t [ j ]))) ≡
      proj₁ (eval-lax P A B k (t [ k ]))
-}

mutual
  eval-fst : (P : Poly) (A B : PSh) (i : Size)
    → PSh.Obj (eval P (Prod A B)) i → PSh.Obj (eval P A) i 
  eval-fst I A B i = proj₁
  eval-fst (P ⊞ P₁) A B i (inj₁ x) = inj₁ (eval-fst P A B i x)
  eval-fst (P ⊞ P₁) A B i (inj₂ y) = inj₂ (eval-fst P₁ A B i y)
  proj₁ (eval-fst (P ⊠ P₁) A B i (x , y)) = eval-fst P A B i x
  proj₂ (eval-fst (P ⊠ P₁) A B i (x , y)) = eval-fst P₁ A B i y
  proj₁ (eval-fst (► P) A B i (t , p)) [ j ] = eval-fst P A B j (t [ j ])
  proj₂ (eval-fst (► P) A B i (t , p)) j k =
    trans (eval-fst-eq P A B j k (t [ j ])) (cong (eval-fst P A B k) (p j k))
  eval-fst (∁ X) A B i t = t

  eval-fst-eq : (P : Poly) (A B : PSh) (i : Size) (j : Size≤ i)
    → (t : PSh.Obj (eval P (Prod A B)) i)
    → PSh.Mor (eval P A) i j (eval-fst P A B i t) ≡ eval-fst P A B j (PSh.Mor (eval P (Prod A B)) i j t)
  eval-fst-eq I A B i j t = refl
  eval-fst-eq (P ⊞ P₁) A B i j (inj₁ x) = cong inj₁ (eval-fst-eq P A B i j x)
  eval-fst-eq (P ⊞ P₁) A B i j (inj₂ y) = cong inj₂ (eval-fst-eq P₁ A B i j y)
  eval-fst-eq (P ⊠ P₁) A B i j (x , y) = cong₂ _,_ (eval-fst-eq P A B i j x) (eval-fst-eq P₁ A B i j y)
  eval-fst-eq (► P) A B i j (t , p) = ▻Obj-eq {eval P A} (funext (λ { [ k ] → refl }))
  eval-fst-eq (∁ X) A B i j t = refl

primrec : (P : Poly) (Γ : Ctx tot) (A : Ty tot)
  → Tm tot Γ (eval P (μ P ⊗ A) ⇒ A) → Tm tot Γ (μ P ⇒ A)
proj₁ (proj₁ (primrec P Γ A (t , p)) i γ) j x = {!proj₁ (t i γ) j!}
proj₂ (proj₁ (primrec P Γ A (t , p)) i γ) = {!!}
proj₂ (primrec P Γ A (t , p)) = {!!}

{-
primrec : (P : Poly) (Γ : Ctx tot) (A : Ty tot)
  → Tm tot Γ (eval P (μ P ⊗ A) ⇒ A) → Tm tot Γ (μ P ⇒ A)
proj₁ (proj₁ (primrec P Γ A (t , p)) i γ) j x = proj₁ (t i γ) j {!proj₁ (proj₁ (primrec P Γ A (t , p)) j (PSh.Mor Γ i j γ)) !} 
proj₂ (proj₁ (primrec P Γ A (t , p)) i γ) = {!!}
proj₂ (primrec P Γ A (t , p)) = {!!}
-}


{-

data MuObj (P : Poly) : Poly → Size → Set where
  supI : ∀ {i} → MuObj P P i → MuObj P I i
  sup⊠ : ∀ {Q₁ Q₂ i} → MuObj P Q₁ i → MuObj P Q₂ i → MuObj P (Q₁ ⊠ Q₂) i
  sup⊞₁ : ∀ {Q₁ Q₂ i} → MuObj P Q₁ i → MuObj P (Q₁ ⊞ Q₂) i
  sup⊞₂ : ∀ {Q₁ Q₂ i} → MuObj P Q₂ i → MuObj P (Q₁ ⊞ Q₂) i
  sup► : ∀ {Q i} → Later (MuObj P Q) i → MuObj P (► Q) i
  sup∁ : ∀ {X i} → X → MuObj P (∁ X) i

MuMor : (P Q : Poly) (i : Size) (j : Size≤ i) → MuObj P Q i → MuObj P Q j
MuMor P I i j (supI t) = supI (MuMor P P i j t)
MuMor P (Q₁ ⊠ Q₂) i j (sup⊠ t u) = sup⊠ (MuMor P Q₁ i j t) (MuMor P Q₂ i j u)
MuMor P (Q₁ ⊞ Q₂) i j (sup⊞₁ t) = sup⊞₁ (MuMor P Q₁ i j t)
MuMor P (Q₁ ⊞ Q₂) i j (sup⊞₂ t) = sup⊞₂ (MuMor P Q₂ i j t)
MuMor P (► Q) i j (sup► t) = sup► t
MuMor P (∁ X) i j (sup∁ x) = sup∁ x

MuMorId : (P Q : Poly) {i : Size} {x : MuObj P Q i} → MuMor P Q i i x ≡ x
MuMorId P I {_} {supI t} = cong supI (MuMorId P P)
MuMorId P (Q₁ ⊠ Q₂) {_} {sup⊠ t u} = cong₂ sup⊠ (MuMorId P Q₁) (MuMorId P Q₂)
MuMorId P (Q₁ ⊞ Q₂) {_} {sup⊞₁ t} = cong sup⊞₁ (MuMorId P Q₁)
MuMorId P (Q₁ ⊞ Q₂) {_} {sup⊞₂ t} = cong sup⊞₂ (MuMorId P Q₂)
MuMorId P (► Q) {_} {sup► t} = refl
MuMorId P (∁ X) {_} {sup∁ x} = refl

MuMorComp : (P Q : Poly) {i : Size} {j : Size≤ i} {k : Size≤ j} {x : MuObj P Q i}
  → MuMor P Q i k x ≡ MuMor P Q j k (MuMor P Q i j x)
MuMorComp P I {_} {_} {_} {supI t} = cong supI (MuMorComp P P)
MuMorComp P (Q₁ ⊠ Q₂) {_} {_} {_} {sup⊠ t u} = cong₂ sup⊠ (MuMorComp P Q₁) (MuMorComp P Q₂)
MuMorComp P (Q₁ ⊞ Q₂) {_} {_} {_} {sup⊞₁ t} = cong sup⊞₁ (MuMorComp P Q₁)
MuMorComp P (Q₁ ⊞ Q₂) {_} {_} {_} {sup⊞₂ t} = cong sup⊞₂ (MuMorComp P Q₂)
MuMorComp P (► Q) {_} {_} {_} {sup► t} = refl
MuMorComp P (∁ X) {_} {_} {_} {sup∁ x} = refl

Mu : Poly → PSh
Mu P = record
  { Obj = MuObj P P
  ; Mor = MuMor P P
  ; MorId = MuMorId P P
  ; MorComp = MuMorComp P P
  }

eval : (P : Poly) → PSh → PSh
eval I A = A
eval (P ⊞ Q) A = Sum (eval P A) (eval Q A)
eval (P ⊠ Q) A = Prod (eval P A) (eval Q A)
eval (► P) A = ▻ (eval P A)
eval (∁ Q) A = WC Q

μ : Poly → Ty tot
μ = Mu

cons₁ : (P Q : Poly) (i : Size) → PSh.Obj (eval Q (μ P)) i → MuObj P Q i
cons₁ P I i t = supI t
cons₁ P (Q₁ ⊞ Q₂) i (inj₁ t) = sup⊞₁ (cons₁ P Q₁ i t)
cons₁ P (Q₁ ⊞ Q₂) i (inj₂ t) = sup⊞₂ (cons₁ P Q₂ i t)
cons₁ P (Q₁ ⊠ Q₂) i (t₁ , t₂) = sup⊠ (cons₁ P Q₁ i t₁) (cons₁ P Q₂ i t₂)
cons₁ P (► Q) i (t , p) = sup► (λ { [ j ] → cons₁ P Q j (t [ j ]) })
cons₁ P (∁ X) i t = sup∁ t

cons₂ : (P Q : Poly) (i : Size) (j : Size≤ i) (t : PSh.Obj (eval Q (μ P)) i)
  → MuMor P Q i j (cons₁ P Q i t) ≡ cons₁ P Q j (PSh.Mor (eval Q (μ P)) i j t)
cons₂ P I i j t = refl
cons₂ P (Q₁ ⊞ Q₂) i j (inj₁ t) = cong sup⊞₁ (cons₂ P Q₁ i j t)
cons₂ P (Q₁ ⊞ Q₂) i j (inj₂ t) = cong sup⊞₂ (cons₂ P Q₂ i j t)
cons₂ P (Q₁ ⊠ Q₂) i j (t₁ , t₂) = cong₂ sup⊠ (cons₂ P Q₁ i j t₁) (cons₂ P Q₂ i j t₂)
cons₂ P (► Q) i j (t , p) = cong sup► (funext (λ { [ k ] → refl }))
cons₂ P (∁ X) i j t = refl

cons : (P : Poly) (Γ : Ctx tot) → Tm tot Γ (eval P (μ P)) → Tm tot Γ (μ P)
proj₁ (cons P Γ (t , p)) i γ = cons₁ P P i (t i γ)
proj₂ (cons P Γ (t , p)) i j γ =
  begin
    MuMor P P i j (cons₁ P P i (t i γ))
  ≡⟨ cons₂ P P i j (t i γ) ⟩
    cons₁ P P j (PSh.Mor (eval P (Mu P)) i j (t i γ))
  ≡⟨ cong (cons₁ P P j) (p i j γ) ⟩
    cons₁ P P j (t j (PSh.Mor Γ i j γ))
  ∎

mutual
  primrec₁₁ : (P Q : Poly) (i : Size) → MuObj P Q i → PSh.Obj (eval Q (Mu P)) i
  primrec₁₁ P I i (supI t) = t
  primrec₁₁ P (Q₁ ⊞ Q₂) i (sup⊞₁ t) = inj₁ (primrec₁₁ P Q₁ i t)
  primrec₁₁ P (Q₁ ⊞ Q₂) i (sup⊞₂ t) = inj₂ (primrec₁₁ P Q₂ i t)
  primrec₁₁ P (Q₁ ⊠ Q₂) i (sup⊠ t₁ t₂) = primrec₁₁ P Q₁ i t₁ , primrec₁₁ P Q₂ i t₂
  primrec₁₁ P (► Q) i (sup► t) =
    (λ { [ j ] → primrec₁₁ P Q j (t [ j ]) }) ,
    (λ { j k → trans (primrec₁₂ P Q j k (t [ j ])) (cong (primrec₁₁ P Q k) {!!}) })
  primrec₁₁ P (∁ X) i (sup∁ x) = x

  primrec₁₂ : (P Q : Poly) (i : Size) (j : Size≤ i) (t : MuObj P Q i) 
    → PSh.Mor (eval Q (Mu P)) i j (primrec₁₁ P Q i t) ≡ primrec₁₁ P Q j (MuMor P Q i j t)
  primrec₁₂ P I i j (supI t) = refl
  primrec₁₂ P (Q₁ ⊞ Q₂) i j (sup⊞₁ t) = cong inj₁ (primrec₁₂ P Q₁ i j t)
  primrec₁₂ P (Q₁ ⊞ Q₂) i j (sup⊞₂ t) = cong inj₂ (primrec₁₂ P Q₂ i j t)
  primrec₁₂ P (Q₁ ⊠ Q₂) i j (sup⊠ t₁ t₂) = cong₂ _,_ (primrec₁₂ P Q₁ i j t₁) (primrec₁₂ P Q₂ i j t₂)
  primrec₁₂ P (► Q) i j (sup► t) = {!!}
  primrec₁₂ P (∁ X) i j t = {!!}

{-
primrec₁₁ : (P Q : Poly) (A : Ty tot) (i : Size)
  → ((j : Size≤ i) → PSh.Obj (eval Q (Prod (Mu P) A)) j → PSh.Obj A j)
  → (j : Size≤ i) → MuObj P Q j → PSh.Obj A j
primrec₁₁ P I A i t j (supI x) = primrec₁₁ P P A i (λ k y → t k {!y!}) j x
--t j (x , (primrec₁₁ P P A i (λ k p → {!!}) j x))
primrec₁₁ P (Q₁ ⊞ Q₂) A i t = {!!}
primrec₁₁ P (Q₁ ⊠ Q₂) A i t = {!!}
primrec₁₁ P (► Q) A i t = {!!}
primrec₁₁ P (∁ X) A i t j (sup∁ x) = t j x
-}

primrec : (P : Poly) (Γ : Ctx tot) (A : Ty tot)
  → Tm tot Γ (eval P (μ P ⊗ A) ⇒ A) → Tm tot Γ (μ P ⇒ A)
proj₁ (proj₁ (primrec P Γ A (t , p)) i γ) = {!!} --primrec₁₁ P P A i (proj₁ (t i γ))
proj₂ (proj₁ (primrec P Γ A (t , p)) i γ) = {!!}
proj₂ (primrec P Γ A (t , p)) = {!!}
-}


{-
eval : {b : Bool} → Poly → Ty b → Ty b
eval {set} I A = A
eval {set} (P ⊞ Q) A = eval P A ⊎ eval Q A
eval {set} (P ⊠ Q) A = eval P A × eval Q A
eval {set} (► P) A = eval P A
eval {set} (∁ X) A = X
eval {tot} I A = A
eval {tot} (P ⊞ Q) A = Sum (eval P A) (eval Q A)
eval {tot} (P ⊠ Q) A = Prod (eval P A) (eval Q A)
eval {tot} (► P) A = ▻ (eval P A)
eval {tot} (∁ X) A = WC X
-}

{-
eval : Poly → (Size → Set) → Size → Set
eval I A = A
eval (P ⊞ Q) A i = eval P A i ⊎ eval Q A i
eval (P ⊠ Q) A i = eval P A i × eval Q A i
eval (► P) A = Later (eval P A)
eval (∁ X) A _ = X

evalMor : (P : Poly) (A : Size → Set)
  → ((i : Size) (j : Size≤ i) → A i → A j)
  → (i : Size) (j : Size≤ i) → eval P A i → eval P A j
evalMor I A r = r
evalMor (P ⊞ Q) A r i j = map⊎ (evalMor P A r i j) (evalMor Q A r i j)
evalMor (P ⊠ Q) A r i j = map× (evalMor P A r i j) (evalMor Q A r i j)
evalMor (► P) A r i j x [ k ] = x [ k ] 
evalMor (∁ X) A r i j x = x
-}

{-
data MuObj (P : Poly) (i : Size) : Set where
  sup : eval P (MuObj P) i → MuObj P i

evalMuMor : (P P' : Poly) (i : Size) (j : Size≤ i) → eval P (MuObj P') i → eval P (MuObj P') j
evalMuMor I P' i j (sup t) = sup (evalMuMor P' P' i j t)
evalMuMor (P ⊞ Q) P' i j = map⊎ (evalMuMor P P' i j) (evalMuMor Q P' i j)
evalMuMor (P ⊠ Q) P' i j = map× (evalMuMor P P' i j) (evalMuMor Q P' i j)
evalMuMor (► P) P' i j x [ k ] = x [ k ]
evalMuMor (∁ X) P' i j x = x

Mu : Poly → Ty tot
Mu P = record
  { Obj = MuObj P
  ; Mor = {!!}
  ; MorId = {!!}
  ; MorComp = {!!}
  }
-}
