module CloTT.TypeFormers.Mu where

open import Data.Sum renaming (map to map⊎)
open import Data.Product renaming (map to map×)
open import Prelude
open import Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers

-- Grammar for polynomials
data Poly : Set₁ where
  ∁ : Set → Poly
  I : Poly
  _⊞_ _⊠_ : Poly → Poly → Poly
  _⇛_ : Set → Poly → Poly
  ► : Poly → Poly

-- Evaluation of polynomials in presheaves
evalObj : Poly → (A : Size → Set) → ((i : Size) (j : Size≤ i) → A i → A j) → Size → Set
evalMor : (P : Poly) (A : Size → Set)
  → (A-map : (i : Size) (j : Size≤ i) → A i → A j)
  → (i : Size) (j : Size≤ i) → evalObj P A A-map i → evalObj P A A-map j
evalObj (∁ X) A A-map i = X
evalObj I A A-map i = A i
evalObj (P ⊞ Q) A A-map i = evalObj P A A-map i ⊎ evalObj Q A A-map i
evalObj (P ⊠ Q) A A-map i = evalObj P A A-map i × evalObj Q A A-map i
evalObj (X ⇛ P) A A-map i = X → evalObj P A A-map i
evalObj (► P) A A-map i =
  Σ (Later (evalObj P A A-map) i)
    (λ x → (j : Size< i) (k : Size≤ j) → evalMor P A A-map j k (x [ j ]) ≡ x [ k ])
evalMor (∁ X) A A-map i j x = x
evalMor I A A-map i j x = A-map i j x
evalMor (P ⊞ Q) A A-map i j (inj₁ x) = inj₁ (evalMor P A A-map i j x)
evalMor (P ⊞ Q) A A-map i j (inj₂ x) = inj₂ (evalMor Q A A-map i j x)
evalMor (P ⊠ Q) A A-map i j (x , y) = evalMor P A A-map i j x , evalMor Q A A-map i j y
evalMor (X ⇛ P) A A-map i j f x = evalMor P A A-map i j (f x)
proj₁ (evalMor (► P) A A-map i j (x , p)) = x
proj₂ (evalMor (► P) A A-map i j (x , p)) = p


evalMorId : (P : Poly) (A : PSh)
  → {i : Size} {x : evalObj P (PSh.Obj A) (PSh.Mor A) i} →
      evalMor P (PSh.Obj A) (PSh.Mor A) i i x ≡ x
evalMorId (∁ X) A = refl
evalMorId I A = PSh.MorId A
evalMorId (P ⊞ Q) A {x = inj₁ x} = cong inj₁ (evalMorId P A)
evalMorId (P ⊞ Q) A {x = inj₂ x} = cong inj₂ (evalMorId Q A)
evalMorId (P ⊠ Q) A = cong₂ _,_ (evalMorId P A) (evalMorId Q A)
evalMorId (X ⇛ P) A = funext (λ _ → evalMorId P A)
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
evalMorComp (X ⇛ P) A = funext (λ _ → evalMorComp P A)
evalMorComp (► P) A = refl

eval : Poly → PSh → PSh
eval P A = record
  { Obj = evalObj P (PSh.Obj A) (PSh.Mor A)
  ; Mor = evalMor P (PSh.Obj A) (PSh.Mor A)
  ; MorId = evalMorId P A
  ; MorComp = evalMorComp P A
  }

-- Formation rule
-- PS: The auxiliary function eval-μMor is needed for the termination checker
-- to accept the definition of μObj and μMor. 
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
  eval-μMor P (X ⇛ Q) i j f x = eval-μMor P Q i j (f x)
  proj₁ (eval-μMor P (► Q) i j (x , p)) = x
  proj₂ (eval-μMor P (► Q) i j (x , p)) = p

eval-μMor-eq : (P Q : Poly) {i : Size} {j : Size≤ i} {x : evalObj Q (μObj P) (μMor P) i}
  → eval-μMor P Q i j x ≡ evalMor Q (μObj P) (μMor P) i j x
eval-μMor-eq P (∁ X) = refl
eval-μMor-eq P I = refl
eval-μMor-eq P (Q ⊞ R) {x = inj₁ x} = cong inj₁ (eval-μMor-eq P Q)
eval-μMor-eq P (Q ⊞ R) {x = inj₂ x} = cong inj₂ (eval-μMor-eq P R)
eval-μMor-eq P (Q ⊠ R) = cong₂ _,_ (eval-μMor-eq P Q) (eval-μMor-eq P R)
eval-μMor-eq P (X ⇛ Q) = funext (λ _ → eval-μMor-eq P Q)
eval-μMor-eq P (► Q) = refl

μMorId : (P : Poly) {i : Size} {x : μObj P i} → μMor P i i x ≡ x
eval-μMorId : (P Q : Poly) {i : Size} {x : evalObj Q (μObj P) (μMor P) i} → eval-μMor P Q i i x ≡ x
μMorId P {x = sup x} = cong sup (eval-μMorId P P)
eval-μMorId P (∁ X) = refl
eval-μMorId P I = μMorId P
eval-μMorId P (Q ⊞ R) {x = inj₁ x} = cong inj₁ (eval-μMorId P Q)
eval-μMorId P (Q ⊞ R) {x = inj₂ y} = cong inj₂ (eval-μMorId P R)
eval-μMorId P (Q ⊠ R) = cong₂ _,_ (eval-μMorId P Q) (eval-μMorId P R)
eval-μMorId P (X ⇛ Q) = funext (λ _ → eval-μMorId P Q)
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
eval-μMorComp P (X ⇛ Q) = funext (λ _ → eval-μMorComp P Q)
eval-μMorComp P (► Q) = refl

μ : Poly → PSh
μ P = record
  { Obj = μObj P
  ; Mor = μMor P
  ; MorId = μMorId P
  ; MorComp = μMorComp P
  }

-- Introduction rule
cons : (P : Poly) (Γ : Ctx tot) → Tm tot Γ (eval P (μ P)) → Tm tot Γ (μ P)
proj₁ (cons P Γ (t , p)) i γ = sup (t i γ)
proj₂ (cons P Γ (t , p)) i j γ = cong sup (trans (eval-μMor-eq P P) (p i j γ))

-- Elimination rule
primrec₁₁ : (P Q : Poly) (A : Ty tot) (i : Size)
  → (f : (j : Size≤ i) → evalObj P (ProdObj (μ P) A) (ProdMor (μ P) A) j → PSh.Obj A j)
  → (p : (j : Size≤ i)(k : Size≤ j)(x : evalObj P (ProdObj (μ P) A) (ProdMor (μ P) A) j)
       → PSh.Mor A j k (f j x) ≡ f k (evalMor P _ _ j k x))
  →  (j : Size≤ i) (t : evalObj Q (μObj P) (μMor P) j)
  → evalObj Q (ProdObj (μ P) A) (ProdMor (μ P) A) j
primrec₁₂ : (P Q : Poly) (A : Ty tot) (i : Size)
  → (f : (j : Size≤ i) → evalObj P (ProdObj (μ P) A) (ProdMor (μ P) A) j → PSh.Obj A j)
  → (p : (j : Size≤ i)(k : Size≤ j)(x : evalObj P (ProdObj (μ P) A) (ProdMor (μ P) A) j)
       → PSh.Mor A j k (f j x) ≡ f k (evalMor P _ _ j k x))
  →  (j : Size≤ i) (k : Size≤ j)
  → (t : evalObj Q (μObj P) (μMor P) j) (t' : evalObj Q (μObj P) (μMor P) k)
  → (r : evalMor Q (μObj P) (μMor P) j k t ≡ t')
  → evalMor Q _ _ j k (primrec₁₁ P Q A i f p j t) ≡ primrec₁₁ P Q A i f p k t'
primrec₁₁ P (∁ X) A i f p j t = t
proj₁ (primrec₁₁ P I A i f p j (sup t)) = sup t
proj₂ (primrec₁₁ P I A i f p j (sup t)) = f j (primrec₁₁ P P A i f p j t)
primrec₁₁ P (Q ⊞ R) A i f p j (inj₁ t) = inj₁ (primrec₁₁ P Q A i f p j t)
primrec₁₁ P (Q ⊞ R) A i f p j (inj₂ t) = inj₂ (primrec₁₁ P R A i f p j t)
proj₁ (primrec₁₁ P (Q ⊠ R) A i f p j (t₁ , t₂)) = primrec₁₁ P Q A i f p j t₁
proj₂ (primrec₁₁ P (Q ⊠ R) A i f p j (t₁ , t₂)) = primrec₁₁ P R A i f p j t₂
primrec₁₁ P (X ⇛ Q) A i f p j g x = primrec₁₁ P Q A i f p j (g x)
proj₁ (primrec₁₁ P (► Q) A i f p j (t , q)) [ k ] = primrec₁₁ P Q A i f p k (t [ k ])
proj₂ (primrec₁₁ P (► Q) A i f p j (t , q)) k l = primrec₁₂ P Q A i f p k l _ _ (q k l)
primrec₁₂ P (∁ X) A i f p j k t _ refl = refl
primrec₁₂ P I A i f p j k (sup t) _ refl =
  cong₂ _,_ refl (trans (p j k _) (cong (f k) (primrec₁₂ P P A i f p j k t _ (sym (eval-μMor-eq P P)))))
primrec₁₂ P (Q ⊞ R) A i f p j k (inj₁ t) _ refl = cong inj₁ (primrec₁₂ P Q A i f p j k t _ refl)
primrec₁₂ P (Q ⊞ R) A i f p j k (inj₂ t) _ refl = cong inj₂ (primrec₁₂ P R A i f p j k t _ refl)
primrec₁₂ P (Q ⊠ R) A i f p j k (t₁ , t₂) _ refl =
  cong₂ _,_ (primrec₁₂ P Q A i f p j k t₁ _ refl) (primrec₁₂ P R A i f p j k t₂ _ refl)
primrec₁₂ P (X ⇛ Q) A i f p j k g g' r = funext (λ x → primrec₁₂ P Q A i f p j k (g x) (g' x) (cong-app r x))
primrec₁₂ P (► Q) A i f p j k (t , q) _ refl =
  Σ≡-uip (funext (λ { _ → funext (λ _ → uip)})) (funext (λ { [ l ] → refl }))

primrec₂ : (P Q : Poly) (Γ : Ctx tot) (A : Ty tot)
  → (f : Tm tot Γ (eval P (μ P ⊗ A) ⇒ A))
  → (i : Size) (j : Size≤ i) (γ : PSh.Obj Γ i)
  → (k : Size≤ j) (t : evalObj Q (μObj P) (μMor P) k)
  → primrec₁₁ P Q A i (proj₁ (proj₁ f i γ)) (proj₂ (proj₁ f i γ)) k t ≡
    primrec₁₁ P Q A j (proj₁ (proj₁ f j (PSh.Mor Γ i j γ))) (proj₂ (proj₁ f j (PSh.Mor Γ i j γ))) k t
primrec₂ P (∁ X) Γ A f i j γ k t = refl
primrec₂ P I Γ A (f , p) i j γ k (sup t) =
  cong₂ _,_ refl (cong₂ (λ a b → proj₁ a k b) (p i j _) (primrec₂ P P Γ A (f , p) i j γ k t))
primrec₂ P (Q ⊞ R) Γ A f i j γ k (inj₁ t) = cong inj₁ (primrec₂ P Q Γ A f i j γ k t)
primrec₂ P (Q ⊞ R) Γ A f i j γ k (inj₂ t) = cong inj₂ (primrec₂ P R Γ A f i j γ k t)
primrec₂ P (Q ⊠ R) Γ A f i j γ k (t₁ , t₂) = cong₂ _,_ (primrec₂ P Q Γ A f i j γ k t₁) (primrec₂ P R Γ A f i j γ k t₂)
primrec₂ P (X ⇛ Q) Γ A f i j γ k g = funext (λ x → primrec₂ P Q Γ A f i j γ k (g x))
primrec₂ P (► Q) Γ A f i j γ k (t , q) =
  Σ≡-uip (funext (λ { _ → funext (λ _ → uip) })) (funext (λ { [ l ] → primrec₂ P Q Γ A f i j γ l (t [ l ]) }))

primrec : (P : Poly) (Γ : Ctx tot) (A : Ty tot)
  → Tm tot Γ (eval P (μ P ⊗ A) ⇒ A) → Tm tot Γ (μ P ⇒ A)
proj₁ (proj₁ (primrec P Γ A (f , p)) i γ) j (sup t) =
  proj₁ (f i γ) j (primrec₁₁ P P A i (proj₁ (f i γ)) (proj₂ (f i γ)) j t)
proj₂ (proj₁ (primrec P Γ A (f , p)) i γ) j k (sup t) =
  trans (proj₂ (f i γ) j k _)
        (cong (proj₁ (f i γ) k) (primrec₁₂ P P A i (proj₁ (f i γ)) (proj₂ (f i γ)) j k t _ (sym (eval-μMor-eq P P))))
proj₂ (primrec P Γ A (f , p)) i j γ =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ k → funext (λ { (sup t) → cong₂ (λ a b → proj₁ a k b) (p i j _) (primrec₂ P P Γ A (f , p) i j γ k t) })))


gStr : Ty tot
gStr = μ (∁ ℕ ⊠ ► I)

Str : Ty set
Str = □ gStr

test = {!!}
