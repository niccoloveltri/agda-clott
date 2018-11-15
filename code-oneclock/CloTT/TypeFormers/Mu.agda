module CloTT.TypeFormers.Mu where

open import Data.Sum renaming (map to map⊎)
open import Data.Product renaming (map to map×)
open import Prelude
open import Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers

data Poly : Set₁ where
  ∁ : Set → Poly
  I : Poly
  _⊞_ _⊠_ : Poly → Poly → Poly
  ► : Poly → Poly

evalObj : Poly → (A : Size → Set) → ((i : Size) (j : Size≤ i) → A i → A j) → Size → Set
evalMor : (P : Poly) (A : Size → Set)
  → (A-map : (i : Size) (j : Size≤ i) → A i → A j)
  → (i : Size) (j : Size≤ i) → evalObj P A A-map i → evalObj P A A-map j
evalObj (∁ X) A A-map i = X
evalObj I A A-map i = A i
evalObj (P ⊞ Q) A A-map i = evalObj P A A-map i ⊎ evalObj Q A A-map i
evalObj (P ⊠ Q) A A-map i = evalObj P A A-map i × evalObj Q A A-map i
evalObj (► P) A A-map i =
  Σ (Later (evalObj P A A-map) i)
    (λ x → (j : Size< i) (k : Size≤ j) → evalMor P A A-map j k (x [ j ]) ≡ x [ k ])
evalMor (∁ X) A A-map i j x = x
evalMor I A A-map i j x = A-map i j x
evalMor (P ⊞ Q) A A-map i j (inj₁ x) = inj₁ (evalMor P A A-map i j x)
evalMor (P ⊞ Q) A A-map i j (inj₂ x) = inj₂ (evalMor Q A A-map i j x)
evalMor (P ⊠ Q) A A-map i j (x , y) = evalMor P A A-map i j x , evalMor Q A A-map i j y
proj₁ (evalMor (► P) A A-map i j (x , p)) = x
proj₂ (evalMor (► P) A A-map i j (x , p)) = p

mutual
  data μObj (P : Poly) (i : Size) : Set where
    sup : evalObj P (μObj P) (μMor P) i → μObj P i

  μMor : (P : Poly) (i : Size) (j : Size≤ i) → μObj P i → μObj P j
  μMor P i j (sup t) = sup (eval-μMor P P i j t)

  eval-μMor : (P Q : Poly) (i : Size) (j : Size≤ i)
    → evalObj Q (μObj P) (μMor P) i → evalObj Q (μObj P) (μMor P) j
  eval-μMor P (∁ X) i j x = x
  eval-μMor P I i j x = μMor P i j x
  eval-μMor P (Q ⊞ R) i j (inj₁ x) = inj₁ (eval-μMor P Q i j x)
  eval-μMor P (Q ⊞ R) i j (inj₂ x) = inj₂ (eval-μMor P R i j x)
  proj₁ (eval-μMor P (Q ⊠ R) i j (x , y)) = eval-μMor P Q i j x
  proj₂ (eval-μMor P (Q ⊠ R) i j (x , y)) = eval-μMor P R i j y
  proj₁ (eval-μMor P (► Q) i j (x , p)) = x
  proj₂ (eval-μMor P (► Q) i j (x , p)) = p


μMorId : (P : Poly) {i : Size} {x : μObj P i} → μMor P i i x ≡ x
eval-μMorId : (P Q : Poly) {i : Size} {x : evalObj Q (μObj P) (μMor P) i} → eval-μMor P Q i i x ≡ x
μMorId P {x = sup x} = cong sup (eval-μMorId P P)
eval-μMorId P (∁ X) = refl
eval-μMorId P I = μMorId P
eval-μMorId P (Q ⊞ R) {x = inj₁ x} = cong inj₁ (eval-μMorId P Q)
eval-μMorId P (Q ⊞ R) {x = inj₂ y} = cong inj₂ (eval-μMorId P R)
eval-μMorId P (Q ⊠ R) = cong₂ _,_ (eval-μMorId P Q) (eval-μMorId P R)
eval-μMorId P (► Q) = refl

μMorComp : (P : Poly) {i : Size} {j : Size≤ i} {k : Size≤ j}
  → {x : μObj P i} → μMor P i k x ≡ μMor P j k (μMor P i j x)
eval-μMorComp : (P Q : Poly) {i : Size} {j : Size≤ i} {k : Size≤ j}
  → {x : evalObj Q (μObj P) (μMor P) i}
  → eval-μMor P Q i k x ≡ eval-μMor P Q j k (eval-μMor P Q i j x)
μMorComp P {x = sup x} = cong sup (eval-μMorComp P P)
eval-μMorComp P (∁ X) = refl
eval-μMorComp P I = μMorComp P
eval-μMorComp P (Q ⊞ R) {x = inj₁ x} = cong inj₁ (eval-μMorComp P Q)
eval-μMorComp P (Q ⊞ R) {x = inj₂ y} = cong inj₂ (eval-μMorComp P R)
eval-μMorComp P (Q ⊠ R) = cong₂ _,_ (eval-μMorComp P Q) (eval-μMorComp P R)
eval-μMorComp P (► Q) = refl

μ : Poly → PSh
μ P = record
  { Obj = μObj P
  ; Mor = μMor P
  ; MorId = μMorId P
  ; MorComp = μMorComp P
  }

evalMorId : (P : Poly) (A : PSh)
  → {i : Size} {x : evalObj P (PSh.Obj A) (PSh.Mor A) i} →
      evalMor P (PSh.Obj A) (PSh.Mor A) i i x ≡ x
evalMorId (∁ X) A = refl
evalMorId I A = PSh.MorId A
evalMorId (P ⊞ Q) A {x = inj₁ x} = cong inj₁ (evalMorId P A)
evalMorId (P ⊞ Q) A {x = inj₂ x} = cong inj₂ (evalMorId Q A)
evalMorId (P ⊠ Q) A = cong₂ _,_ (evalMorId P A) (evalMorId Q A)
evalMorId (► P) A = refl

evalMorComp : (P : Poly) (A : PSh)
  → {i : Size} {j : Size≤ i} {k : Size≤ j}
  → {x : evalObj P (PSh.Obj A) (PSh.Mor A) i} →
      evalMor P (PSh.Obj A) (PSh.Mor A) i k x ≡
      evalMor P (PSh.Obj A) (PSh.Mor A) j k (evalMor P (PSh.Obj A) (PSh.Mor A) i j x)      
evalMorComp (∁ X) A = refl
evalMorComp I A = PSh.MorComp A
evalMorComp (P ⊞ Q) A {x = inj₁ x} = cong inj₁ (evalMorComp P A)
evalMorComp (P ⊞ Q) A {x = inj₂ x} = cong inj₂ (evalMorComp Q A)
evalMorComp (P ⊠ Q) A = cong₂ _,_ (evalMorComp P A) (evalMorComp Q A)
evalMorComp (► P) A = refl

eval : Poly → PSh → PSh
eval P A = record
  { Obj = evalObj P (PSh.Obj A) (PSh.Mor A)
  ; Mor = evalMor P (PSh.Obj A) (PSh.Mor A)
  ; MorId = evalMorId P A
  ; MorComp = evalMorComp P A
  }

eval-μMor-eq : (P Q : Poly) {i : Size} {j : Size≤ i} {x : evalObj Q (μObj P) (μMor P) i}
  → eval-μMor P Q i j x ≡ evalMor Q (μObj P) (μMor P) i j x
eval-μMor-eq P (∁ X) = refl
eval-μMor-eq P I = refl
eval-μMor-eq P (Q ⊞ R) {x = inj₁ x} = cong inj₁ (eval-μMor-eq P Q)
eval-μMor-eq P (Q ⊞ R) {x = inj₂ x} = cong inj₂ (eval-μMor-eq P R)
eval-μMor-eq P (Q ⊠ R) = cong₂ _,_ (eval-μMor-eq P Q) (eval-μMor-eq P R)
eval-μMor-eq P (► Q) = refl


-- Introduction rule
cons : (P : Poly) (Γ : Ctx tot) → Tm tot Γ (eval P (μ P)) → Tm tot Γ (μ P)
proj₁ (cons P Γ (t , p)) i γ = sup (t i γ)
proj₂ (cons P Γ (t , p)) i j γ = cong sup (trans (eval-μMor-eq P P) (p i j γ))

-- Elimination rule

primrec₁₁ : (P : Poly) (Γ : Ctx tot) (A : Ty tot)
  → Tm tot Γ (eval P (μ P ⊗ A) ⇒ A)
  → (i : Size) (γ : PSh.Obj Γ i) (j : Size≤ i)
  → μObj P j → PSh.Obj A j
primrec₁₂ : (P : Poly) (Γ : Ctx tot) (A : Ty tot)
  → (f : Tm tot Γ (eval P (μ P ⊗ A) ⇒ A))
  → (i : Size) (γ : PSh.Obj Γ i) (j : Size≤ i) (k : Size≤ j)
  → (t : μObj P j) → PSh.Mor A j k (primrec₁₁ P Γ A f i γ j t) ≡ primrec₁₁ P Γ A f i γ k (μMor P j k t)
primrec₂ : (P : Poly) (Γ : Ctx tot) (A : Ty tot)
  → (f : Tm tot Γ (eval P (μ P ⊗ A) ⇒ A))
  → (i : Size) (j : Size≤ i) (γ : PSh.Obj Γ i)
  → ExpMor (μ P) A i j (primrec₁₁ P Γ A f i γ , primrec₁₂ P Γ A f i γ) ≡
    (primrec₁₁ P Γ A f j (PSh.Mor Γ i j γ) , primrec₁₂ P Γ A f j (PSh.Mor Γ i j γ))
primrec₁₁' : (P Q : Poly) (Γ : Ctx tot) (A : Ty tot)
  → Tm tot Γ (eval P (μ P ⊗ A) ⇒ A)
  → (i : Size) (γ : PSh.Obj Γ i) (j : Size≤ i)
  → evalObj Q (μObj P) (μMor P) j → evalObj Q (ProdObj (μ P) A) (ProdMor (μ P) A) j
primrec₁₂' : (P Q : Poly) (Γ : Ctx tot) (A : Ty tot)
  → (f : Tm tot Γ (eval P (μ P ⊗ A) ⇒ A))
  → (i : Size) (γ : PSh.Obj Γ i) (j : Size≤ i) (k : Size≤ j)
  → (t : evalObj Q (μObj P) (μMor P) j)
  → evalMor Q _ _ j k (primrec₁₁' P Q Γ A f i γ j t) ≡ primrec₁₁' P Q Γ A f i γ k (evalMor Q _ _ j k t)
primrec₂' : (P Q : Poly) (Γ : Ctx tot) (A : Ty tot)
  → (f : Tm tot Γ (eval P (μ P ⊗ A) ⇒ A))
  → (i : Size) (j : Size≤ i) (γ : PSh.Obj Γ i)
  → ExpMor (eval Q (μ P)) (eval Q (Prod (μ P) A)) i j (primrec₁₁' P Q Γ A f i γ , primrec₁₂' P Q Γ A f i γ) ≡
    (primrec₁₁' P Q Γ A f j (PSh.Mor Γ i j γ) , primrec₁₂' P Q Γ A f j (PSh.Mor Γ i j γ))

primrec₁₁ P Γ A (f , p) i γ j (sup t) = proj₁ (f i γ) j (primrec₁₁' P P Γ A (f , p) i γ j t)
primrec₁₂ P Γ A (f , p) i γ j k (sup t) =
  trans (proj₂ (f i γ) j k _) (cong (proj₁ (f i γ) k)
        (trans (primrec₁₂' P P Γ A (f , p) i γ j k t)
               (cong (primrec₁₁' P P Γ A (f , p) i γ k) (sym (eval-μMor-eq P P)))))
primrec₂ P Γ A (f , p) i j γ =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ k → funext (λ { (sup x) → cong₂ (λ a b → proj₁ a k (proj₁ b k x)) (p i j γ) (primrec₂' P P Γ A (f , p) i j γ) })))

primrec₁₁' P (∁ X) Γ A f i γ j t = t
primrec₁₁' P I Γ A f i γ j t = t , primrec₁₁ P Γ A f i γ j t
primrec₁₁' P (Q ⊞ R) Γ A f i γ j (inj₁ x) = inj₁ (primrec₁₁' P Q Γ A f i γ j x)
primrec₁₁' P (Q ⊞ R) Γ A f i γ j (inj₂ x) = inj₂ (primrec₁₁' P R Γ A f i γ j x)
primrec₁₁' P (Q ⊠ R) Γ A f i γ j (x , y) = (primrec₁₁' P Q Γ A f i γ j x) , (primrec₁₁' P R Γ A f i γ j y)
primrec₁₁' P (► Q) Γ A f i γ j (t , q) =
  (λ { [ k ] → primrec₁₁' P Q Γ A f i γ k (t [ k ]) }) ,
  (λ { k l → trans (primrec₁₂' P Q Γ A f i γ k l (t [ k ])) (cong (primrec₁₁' P Q Γ A f i γ l) (q k l)) })
primrec₁₂' P (∁ X) Γ A f i γ j k t = refl
primrec₁₂' P I Γ A f i γ j k t = cong₂ _,_ refl (primrec₁₂ P Γ A f i γ j k t)
primrec₁₂' P (Q ⊞ R) Γ A f i γ j k (inj₁ x) = cong inj₁ (primrec₁₂' P Q Γ A f i γ j k x)
primrec₁₂' P (Q ⊞ R) Γ A f i γ j k (inj₂ x) = cong inj₂ (primrec₁₂' P R Γ A f i γ j k x)
primrec₁₂' P (Q ⊠ R) Γ A f i γ j k (x , y) = cong₂ _,_ (primrec₁₂' P Q Γ A f i γ j k x) (primrec₁₂' P R Γ A f i γ j k y)
primrec₁₂' P (► Q) Γ A f i γ j k (t , p) =
  Σ≡-uip (funext (λ { _ → funext (λ _ → uip)}))
         (funext (λ { [ l ] → refl }))
primrec₂' P (∁ X) Γ A f i j γ = refl
primrec₂' P I Γ A f i j γ =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ k → funext (λ x → cong₂ _,_ refl (cong (λ a → proj₁ a k x) (primrec₂ P Γ A f i j γ)))))
primrec₂' P (Q ⊞ R) Γ A f i j γ =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ k → funext (λ { (inj₁ x) → cong inj₁ (cong (λ a → proj₁ a k x) (primrec₂' P Q Γ A f i j γ)) ;
                                    (inj₂ y) → cong inj₂ (cong (λ a → proj₁ a k y) (primrec₂' P R Γ A f i j γ)) })))
primrec₂' P (Q ⊠ R) Γ A f i j γ =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ k → funext (λ { (x , y) → cong₂ (λ a b → (proj₁ a k x , proj₁ b k y)) (primrec₂' P Q Γ A f i j γ) (primrec₂' P R Γ A f i j γ) })))
primrec₂' P (► Q) Γ A f i j γ =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ k → funext (λ { (x , p) → Σ≡-uip (funext (λ{  _ → funext (λ _ → uip)}))
                                                     (funext (λ { [ l ] → cong (λ a → proj₁ a l (x [ l ])) (primrec₂' P Q Γ A f i j γ) }))})))

primrec : (P : Poly) (Γ : Ctx tot) (A : Ty tot)
  → Tm tot Γ (eval P (μ P ⊗ A) ⇒ A) → Tm tot Γ (μ P ⇒ A)
proj₁ (proj₁ (primrec P Γ A f) i γ) = primrec₁₁ P Γ A f i γ
proj₂ (proj₁ (primrec P Γ A f) i γ) = primrec₁₂ P Γ A f i γ
proj₂ (primrec P Γ A f) = primrec₂ P Γ A f







{-
primrec : (P : Poly) (Γ : Ctx tot) (A : Ty tot)
  → Tm tot Γ (eval P (μ P ⊗ A) ⇒ A) → Tm tot Γ (μ P ⇒ A)
primrec' : (P Q : Poly) (Γ : Ctx tot) (A : Ty tot)
  → Tm tot Γ (eval P (μ P ⊗ A) ⇒ A) → Tm tot Γ (eval Q (μ P) ⇒ eval Q (μ P ⊗ A))

primrec P Γ A (f , p) =
  (λ i γ → (λ { j (sup t) → proj₁ (f i γ) j (proj₁ (proj₁ (primrec' P P Γ A (f , p)) i γ) j t) }) ,
           {!!}) ,
  {!!}

primrec' P (∁ X) Γ A (f , p) =
  (λ i γ → (λ j t → t) ,
           {!!}) ,
  {!!}
primrec' P I Γ A (f , p) =
  (λ i γ → (λ j t → t , proj₁ (proj₁ (primrec P Γ A (f , p)) i γ) j t) ,
           {!!}) ,
  {!!}
primrec' P (Q ⊞ R) Γ A (f , p) = {!!}
primrec' P (Q ⊠ R) Γ A (f , p) = {!!}
primrec' P (► Q) Γ A (f , p) = {!!}
-}

{-
{-# TERMINATING #-}
primrec : (P : Poly) (Γ : Ctx tot) (A : Ty tot)
  → Tm tot Γ (eval P (μ P ⊗ A) ⇒ A) → Tm tot Γ (μ P ⇒ A)
primrec' : (P Q : Poly) (Γ : Ctx tot) (A : Ty tot)
  → Tm tot Γ (eval P (μ P ⊗ A) ⇒ A) → Tm tot Γ (eval Q (μ P) ⇒ eval Q (μ P ⊗ A))

proj₁ (proj₁ (primrec P Γ A (f , p)) i γ) j (sup t) = proj₁ (f i γ) j (proj₁ (proj₁ (primrec' P P Γ A (f , p)) i γ) j t)

proj₂ (proj₁ (primrec P Γ A (f , p)) i γ) j k (sup x) =
  trans (proj₂ (f i γ) j k (proj₁ (proj₁ (primrec' P P Γ A (f , p)) i γ) j x))
        (cong (proj₁ (f i γ) k) (trans (proj₂ (proj₁ (primrec' P P Γ A (f , p)) i γ) j k x)
                                       (cong (proj₁ (proj₁ (primrec' P P Γ A (f , p)) i γ) k) (sym (eval-μMor-eq P P)))))

proj₂ (primrec P Γ A (f , p)) i j γ =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ k → funext (λ { (sup x) → cong₂ (λ a b → proj₁ a k (proj₁ b k x)) (p i j γ) (proj₂ (primrec' P P Γ A (f , p)) i j γ) })))

proj₁ (proj₁ (primrec' P (∁ X) Γ A (f , p)) i γ) j t = t
proj₁ (proj₁ (proj₁ (primrec' P I Γ A (f , p)) i γ) j t) = t
proj₂ (proj₁ (proj₁ (primrec' P I Γ A (f , p)) i γ) j t) = proj₁ (proj₁ (primrec P Γ A (f , p)) i γ) j t
proj₁ (proj₁ (primrec' P (Q ⊞ R) Γ A (f , p)) i γ) j (inj₁ x) = inj₁ (proj₁ (proj₁ (primrec' P Q Γ A (f , p)) i γ) j x)
proj₁ (proj₁ (primrec' P (Q ⊞ R) Γ A (f , p)) i γ) j (inj₂ x) = inj₂ (proj₁ (proj₁ (primrec' P R Γ A (f , p)) i γ) j x)
proj₁ (proj₁ (proj₁ (primrec' P (Q ⊠ R) Γ A (f , p)) i γ) j (x , y)) = proj₁ (proj₁ (primrec' P Q Γ A (f , p)) i γ) j x
proj₂ (proj₁ (proj₁ (primrec' P (Q ⊠ R) Γ A (f , p)) i γ) j (x , y)) = proj₁ (proj₁ (primrec' P R Γ A (f , p)) i γ) j y
proj₁ (proj₁ (proj₁ (primrec' P (► Q) Γ A (f , p)) i γ) j (t , q)) [ k ] = proj₁ (proj₁ (primrec' P Q Γ A (f , p)) j (PSh.Mor Γ i j γ)) k (t [ k ])
proj₂ (proj₁ (proj₁ (primrec' P (► Q) Γ A (f , p)) i γ) j (t , q)) k l =
  trans (proj₂ (proj₁ (primrec' P Q Γ A (f , p)) j (PSh.Mor Γ i j γ)) k l (t [ k ]))
        (cong (proj₁ (proj₁ (primrec' P Q Γ A (f , p)) j (PSh.Mor Γ i j γ)) l) (q k l))

proj₂ (proj₁ (primrec' P (∁ X) Γ A (f , p)) i γ) j k x = refl
proj₂ (proj₁ (primrec' P I Γ A (f , p)) i γ) j k x = cong₂ _,_ refl (proj₂ (proj₁ (primrec P Γ A (f , p)) i γ) j k x)
proj₂ (proj₁ (primrec' P (Q ⊞ R) Γ A (f , p)) i γ) j k (inj₁ x) = cong inj₁ (proj₂ (proj₁ (primrec' P Q Γ A (f , p)) i γ) j k x)
proj₂ (proj₁ (primrec' P (Q ⊞ R) Γ A (f , p)) i γ) j k (inj₂ x) = cong inj₂ (proj₂ (proj₁ (primrec' P R Γ A (f , p)) i γ) j k x)
proj₂ (proj₁ (primrec' P (Q ⊠ R) Γ A (f , p)) i γ) j k (x , y) =
  cong₂ _,_ (proj₂ (proj₁ (primrec' P Q Γ A (f , p)) i γ) j k x) (proj₂ (proj₁ (primrec' P R Γ A (f , p)) i γ) j k y)
proj₂ (proj₁ (primrec' P (► Q) Γ A (f , p)) i γ) j k x = {!!}

proj₂ (primrec' P Q Γ A (f , p)) i j γ = {!!}
-}




{-
data Poly : Set₁ where
  I : Poly
  _⊠_ : (P Q : Poly) → Poly
  ∁ : (X : Set) → Poly

{-
data MuObj (P : Poly) : Poly → Size → Set where
  supI : ∀ {i} → MuObj P P i → MuObj P I i
  sup⊠ : ∀ {Q₁ Q₂ i} → MuObj P Q₁ i → MuObj P Q₂ i → MuObj P (Q₁ ⊠ Q₂) i
  sup∁ : ∀ {X i} → X → MuObj P (∁ X) i

MuMor : (P Q : Poly) (i : Size) (j : Size≤ i) → MuObj P Q i → MuObj P Q j
MuMor P I i j (supI t) = supI (MuMor P P i j t)
MuMor P (Q ⊠ R) i j (sup⊠ t u) = sup⊠ (MuMor P Q i j t) (MuMor P R i j u)
MuMor P (∁ X) i j (sup∁ x) = sup∁ x

MuMorId : (P Q : Poly) {i : Size} {x : MuObj P Q i} → MuMor P Q i i x ≡ x
MuMorId P I {x = supI x} = cong supI (MuMorId P P)
MuMorId P (Q ⊠ R) {x = sup⊠ x y} = cong₂ sup⊠ (MuMorId P Q) (MuMorId P R)
MuMorId P (∁ X) {x = sup∁ x} = refl

MuMorComp : (P Q : Poly) {i : Size} {j : Size≤ i} {k : Size≤ j} {x : MuObj P Q i}
  → MuMor P Q i k x ≡ MuMor P Q j k (MuMor P Q i j x)
MuMorComp = {!!}

Mu : Poly → Poly → PSh
Mu P Q = record
  { Obj = MuObj P Q
  ; Mor = MuMor P Q
  ; MorId = MuMorId P Q
  ; MorComp = MuMorComp P Q
  }
-}

evalObj : Poly → (Size → Set) → Size → Set
evalObj I A = A
evalObj (P ⊠ Q) A i = evalObj P A i × evalObj Q A i
evalObj (∁ X) A i = X

evalObj-map : (P : Poly) (A B : Size → Set) (i : Size)
  → (f : (j : Size≤ i) → A j → B j)
  → (j : Size≤ i) → evalObj P A j → evalObj P B j
evalObj-map P A B i f j t = {!!}

eval : Poly → PSh → PSh
eval P A = record
  { Obj = evalObj P (PSh.Obj A)
  ; Mor = {!!}
  ; MorId = {!!}
  ; MorComp = {!!}
  }

data μ (P : Poly) (i : Size) : Set where
-}

{-
μObj : Poly → Size → Set
μObj P = MuObj P P

μ : Poly → PSh
μ P = Mu P P

fold₁ : (P Q : Poly) (i : Size) → evalObj Q (μObj P) i → MuObj P Q i
fold₁ P I i t = supI t
fold₁ P (Q ⊠ R) i (t , u) = sup⊠ (fold₁ P Q i t) (fold₁ P R i u)
fold₁ P (∁ X) i t = sup∁ t

fold : (P Q : Poly) (Γ : Ctx tot) → Tm tot Γ (eval Q (μ P)) → Tm tot Γ (Mu P Q)
proj₁ (fold P Q Γ (t , p)) i γ = fold₁ P Q i (t i γ)
proj₂ (fold P Q Γ (t , p)) = {!!}

unfold₁ : (P Q : Poly) (i : Size) → MuObj P Q i → evalObj Q (μObj P) i
unfold₁ P Q i t = {!!}

primrec₁₁ : (P Q : Poly) (A : Size → Set) (i : Size)
  → (f : (j : Size≤ i) → evalObj P A j → A j)
  → (j : Size≤ i) → MuObj P Q j → A j
primrec₁₁ P I A i f j (supI t) = f j {!primrec₁₁ P P A i ? j t!} --(evalObj-map P (μObj P) A i (λ k x → primrec₁₁ P P A i f k x) j (unfold₁ P P j t))
primrec₁₁ P (Q ⊠ R) A i f j (sup⊠ t u) = {!!}
primrec₁₁ P (∁ X) A i f j (sup∁ x) = {!!}

primrec : (P Q : Poly) (Γ : Ctx tot) (A : Ty tot)
  → Tm tot Γ (eval Q (μ P ⊗ A) ⇒ A) → Tm tot Γ (Mu P Q ⇒ A)
proj₁ (proj₁ (primrec P Q Γ A (t , p)) i γ) j x = {!proj₁ (t i γ) j!}
proj₂ (proj₁ (primrec P Q Γ A (t , p)) i γ) = {!!}
proj₂ (primrec P Q Γ A (t , p)) = {!!}
-}

{-
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

eval-map : (P : Poly) (A B : PSh) (i : Size)
  → ((j : Size≤ i) → PSh.Obj A j → PSh.Obj B j)
  → (j : Size≤ i) → PSh.Obj (eval P A) j → PSh.Obj (eval P B) j
eval-map P A B f = {!!}

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

mutual
  eval-snd : (P : Poly) (A B : PSh) (i : Size)
    → PSh.Obj (eval P (Prod A B)) i → PSh.Obj (eval P B) i 
  eval-snd I A B i = proj₂
  eval-snd (P ⊞ P₁) A B i (inj₁ x) = inj₁ (eval-snd P A B i x)
  eval-snd (P ⊞ P₁) A B i (inj₂ y) = inj₂ (eval-snd P₁ A B i y)
  proj₁ (eval-snd (P ⊠ P₁) A B i (x , y)) = eval-snd P A B i x
  proj₂ (eval-snd (P ⊠ P₁) A B i (x , y)) = eval-snd P₁ A B i y
  proj₁ (eval-snd (► P) A B i (t , p)) [ j ] = eval-snd P A B j (t [ j ])
  proj₂ (eval-snd (► P) A B i (t , p)) j k =
    trans (eval-snd-eq P A B j k (t [ j ])) (cong (eval-snd P A B k) (p j k))
  eval-snd (∁ X) A B i t = t

  eval-snd-eq : (P : Poly) (A B : PSh) (i : Size) (j : Size≤ i)
    → (t : PSh.Obj (eval P (Prod A B)) i)
    → PSh.Mor (eval P B) i j (eval-snd P A B i t) ≡ eval-snd P A B j (PSh.Mor (eval P (Prod A B)) i j t)
  eval-snd-eq I A B i j t = refl
  eval-snd-eq (P ⊞ P₁) A B i j (inj₁ x) = cong inj₁ (eval-snd-eq P A B i j x)
  eval-snd-eq (P ⊞ P₁) A B i j (inj₂ y) = cong inj₂ (eval-snd-eq P₁ A B i j y)
  eval-snd-eq (P ⊠ P₁) A B i j (x , y) = cong₂ _,_ (eval-snd-eq P A B i j x) (eval-snd-eq P₁ A B i j y)
  eval-snd-eq (► P) A B i j (t , p) = ▻Obj-eq {eval P B} (funext (λ { [ k ] → refl }))
  eval-snd-eq (∁ X) A B i j t = refl

mutual
  eval-str : (P : Poly) (A B : PSh) (i : Size)
    → PSh.Obj (Prod (eval P A) B) i → PSh.Obj (eval P (Prod A B)) i 
  eval-str I A B i (t , b) = t , b
  eval-str (P₁ ⊞ P₂) A B i (inj₁ x , b) = inj₁ (eval-str P₁ A B i (x , b))
  eval-str (P₁ ⊞ P₂) A B i (inj₂ y , b) = inj₂ (eval-str P₂ A B i (y , b))
  proj₁ (eval-str (P₁ ⊠ P₂) A B i ((x , y) , b)) = eval-str P₁ A B i (x , b)
  proj₂ (eval-str (P₁ ⊠ P₂) A B i ((x , y) , b)) = eval-str P₂ A B i (y , b)
  proj₁ (eval-str (► P) A B i ((t , p) , b)) [ j ] = eval-str P A B j (t [ j ] , PSh.Mor B i j b) 
  proj₂ (eval-str (► P) A B i ((t , p) , b)) j k = {!!} 
  eval-str (∁ X) A B i (t , b) = t


mutual
  primrec₁₁' : (P Q : Poly) (A : Ty tot) (i : Size)
    → ((j : Size≤ i) → ProdObj (Mu P) A j → PSh.Obj A j)
    → (j : Size≤ i) → PSh.Obj (eval Q (Prod (Mu P) A)) j → PSh.Obj A j
--    → (j : Size≤ i) → MuObj P Q j → PSh.Obj (eval Q (Prod (Mu P) A)) j    
  primrec₁₁' P I A i f j (t , x) = x
  primrec₁₁' P (Q₁ ⊞ Q₂) A i f j (inj₁ x) = primrec₁₁' P Q₁ A i f j x
  primrec₁₁' P (Q₁ ⊞ Q₂) A i f j (inj₂ y) = primrec₁₁' P Q₂ A i f j y
  primrec₁₁' P (Q₁ ⊠ Q₂) A i f j (t₁ , t₂) = f j {!!}
--      (proj₁ (eval-map Q₁ (Prod (Mu P) {!!}) (Prod (Mu P) A) {!!}) j {!!})
  primrec₁₁' P (► Q) A i f j t = {!!}
  primrec₁₁' P (∁ X) A i f j t = {!!}

  primrec₁₁ : (P Q : Poly) (A : Ty tot) (i : Size)
    → ((j : Size≤ i) → PSh.Obj (eval Q (Prod (Mu P) A)) j → PSh.Obj A j)
    → (j : Size≤ i) → MuObj P Q j → PSh.Obj A j
  primrec₁₁ P I A i f j (supI t) =
    f j (t , (primrec₁₁ P P A i {!!} j t)) --(primrec₁₁' P P A i f)
  primrec₁₁ P (Q₁ ⊞ Q₂) A i f j (sup⊞₁ t) = primrec₁₁ P Q₁ A i (λ k x → f k (inj₁ x)) j t
  primrec₁₁ P (Q₁ ⊞ Q₂) A i f j (sup⊞₂ t) = primrec₁₁ P Q₂ A i (λ k x → f k (inj₂ x)) j t
  primrec₁₁ P (Q₁ ⊠ Q₂) A i f j (sup⊠ t₁ t₂) =
    f j (eval-str Q₁ (Mu P) A j ((cons-inv₁ P Q₁ j t₁) , primrec₁₁ P Q₁ A i (λ k x → f k (x , {!!})) j t₁) , {!!})
  primrec₁₁ P (► Q) A i f j t = {!!}
  primrec₁₁ P (∁ X) A i f j t = {!!}

{-
  primrec₁₁'' : (P : Poly) (A : Ty tot) (i : Size)
    → ((j : Size≤ i) → PSh.Obj (eval P (Prod (Mu P) A)) j → PSh.Obj A j)
    → (j : Size≤ i) → MuObj P P j → PSh.Obj A j
  primrec₁₁'' I A i f j x = {!!}
  primrec₁₁'' (P ⊞ Q) A i f j x = {!!}
  primrec₁₁'' (P ⊠ Q) A i f j (sup⊠ x y) = f j ((eval-str P (Mu (P ⊠ Q)) A j ((cons-inv₁ _ _ j x) , primrec₁₁'' P A i {!!} j {!!})) , {!!})
  primrec₁₁'' (► P) A i f j x = {!!}
  primrec₁₁'' (∁ X) A i f j x = {!!}
-}

primrec : (P : Poly) (Γ : Ctx tot) (A : Ty tot)
  → Tm tot Γ (eval P (μ P ⊗ A) ⇒ A) → Tm tot Γ (μ P ⇒ A)
proj₁ (proj₁ (primrec P Γ A (t , p)) i γ) j x = {!proj₁ (t i γ) j!}
proj₂ (proj₁ (primrec P Γ A (t , p)) i γ) = {!!}
proj₂ (primrec P Γ A (t , p)) = {!!}

rec₁₁ : (P Q : Poly) (A : Ty tot) (i : Size)
  → ((j : Size≤ i) → PSh.Obj (eval Q A) j → PSh.Obj A j)
  → (j : Size≤ i) → MuObj P Q j → PSh.Obj A j
rec₁₁ P I A i f j (supI t) = {!!}
rec₁₁ P (Q₁ ⊞ Q₂) A i f j (sup⊞₁ t) = {!!} --rec₁₁ P Q₁ A i (λ k x → f k (inj₁ x)) j t
rec₁₁ P (Q₁ ⊞ Q₂) A i f j (sup⊞₂ t) = {!!} --rec₁₁ P Q₂ A i (λ k x → f k (inj₂ x)) j t
rec₁₁ P (Q₁ ⊠ Q₂) A i f j (sup⊠ t₁ t₂) = f j ((eval-map Q₁ (Mu P) A i (rec₁₁ P P A i {!!}) j (cons-inv₁ P Q₁ j t₁)) , {!!})
rec₁₁ P (► Q) A i f j t = {!!}
rec₁₁ P (∁ X) A i f j t = {!!}

rec : (P : Poly) (Γ : Ctx tot) (A : Ty tot)
  → Tm tot Γ (eval P A ⇒ A) → Tm tot Γ (μ P ⇒ A)
proj₁ (proj₁ (rec P Γ A (t , p)) i γ) j x = {!proj₁ (t i γ) j!}
proj₂ (proj₁ (rec P Γ A (t , p)) i γ) = {!!}
proj₂ (rec P Γ A (t , p)) = {!!}

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

-}
