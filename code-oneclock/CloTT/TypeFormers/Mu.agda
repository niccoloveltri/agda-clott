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
