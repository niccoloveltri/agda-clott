\AgdaHide{
\begin{code}
module CloTT.TypeFormers.Mu where

open import Data.Sum renaming (map to map⊎)
open import Data.Product renaming (map to map×)
open import Prelude
open import Prelude.Syntax
open import Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.SumType
open import CloTT.TypeFormers.ProductType
open import CloTT.TypeFormers.FunctionType
open import CloTT.TypeFormers.WeakenClock

open PSh
\end{code}
}

\begin{code}
data SemPoly : tag → Set₁ where
    ∁s : Set → SemPoly set
    ∁ps : PSh → SemPoly tot
    I : {Δ : tag} → SemPoly Δ
    _⊞_ : {Δ : tag} → SemPoly Δ → SemPoly Δ → SemPoly Δ
    _⊠_ : {Δ : tag} → SemPoly Δ → SemPoly Δ → SemPoly Δ
    ► : SemPoly tot → SemPoly tot
\end{code}

\begin{code}
eval : {Δ : tag} → SemPoly Δ → Ty Δ → Ty Δ
eval (∁s A) X = A
eval (∁ps A) X = A
eval I X = X
eval (P ⊞ Q) X = eval P X ⊕ eval Q X
eval (P ⊠ Q) X = eval P X ⊗ eval Q X
eval (► P) X = ▻(eval P X)
\end{code}

\begin{code}
data μset (P : SemPoly set) : SemPoly set → Set where
  ∁s : {X : Set} → X → μset P (∁s X)
  I : μset P P → μset P I
  _⊠_ : {Q R : SemPoly set} → μset P Q → μset P R → μset P (Q ⊠ R)
  ⊞₁ : {Q R : SemPoly set} → μset P Q → μset P (Q ⊞ R)
  ⊞₂ : {Q R : SemPoly set} → μset P R → μset P (Q ⊞ R)
\end{code}

\begin{code}
mutual
  data μObj' (P : SemPoly tot) : SemPoly tot → Size → Set where
    ∁ps : {X : PSh} {i : Size} → Obj X i → μObj' P (∁ps X) i
    I : ∀{i} → μObj' P P i → μObj' P I i
    _⊠_ : ∀{Q}{R}{i} → μObj' P Q i → μObj' P R i → μObj' P (Q ⊠ R) i
    ⊞₁ : ∀{Q}{R}{i} → μObj' P Q i → μObj' P (Q ⊞ R) i
    ⊞₂ : ∀{Q}{R}{i} → μObj' P R i → μObj' P (Q ⊞ R) i
    ► : ∀{Q}{i} (x : Later (μObj' P Q) i) → LaterLim (μObj' P Q) (μMor' P Q) i x → μObj' P (► Q) i

  μMor' : (P Q : SemPoly tot) (i : Size) (j : Size< (↑ i)) → μObj' P Q i → μObj' P Q j
  μMor' P (∁ps X) i j (∁ps x) = ∁ps (Mor X i j x)
  μMor' P I i j (I x) = I (μMor' P P i j x)
  μMor' P (Q ⊠ R) i j (x ⊠ y) = μMor' P Q i j x ⊠ μMor' P R i j y
  μMor' P (Q ⊞ R) i j (⊞₁ x) = ⊞₁ (μMor' P Q i j x)
  μMor' P (Q ⊞ R) i j (⊞₂ x) = ⊞₂ (μMor' P R i j x)
  μMor' P (► Q) i j (► x p) = ► x p'
    where
      p' : LaterLim (μObj' P Q) (μMor' P Q) j x
      p' [ k ] [ l ] = p [ k ] [ l ]
\end{code}

\begin{code}
μMor'Id : (P Q : SemPoly tot) {i : Size} {x : μObj' P Q i} → μMor' P Q i i x ≡ x
μMor'Id P (∁ps X) {i} {∁ps x} = cong ∁ps (MorId X)
μMor'Id P I {i}{I x} = cong I (μMor'Id P P)
μMor'Id P (Q ⊠ R) {i}{x ⊠ y} = cong₂ _⊠_ (μMor'Id P Q) (μMor'Id P R)
μMor'Id P (Q ⊞ R) {i}{⊞₁ x} = cong ⊞₁ (μMor'Id P Q)
μMor'Id P (Q ⊞ R) {i}{⊞₂ x} = cong ⊞₂ (μMor'Id P R)
μMor'Id P (► Q) {i}{► x p} = cong₂-dep ► refl (funext (λ { [ j ] → funext (λ { [ k ] → refl }) }))
\end{code}

\begin{code}
μMor'Comp : (P Q : SemPoly tot) {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)} {x : μObj' P Q i}
  → μMor' P Q i k x ≡ μMor' P Q j k (μMor' P Q i j x)
μMor'Comp P (∁ps X) {x = ∁ps x} = cong ∁ps (MorComp X)
μMor'Comp P I {x = I x} = cong I (μMor'Comp P P)
μMor'Comp P (Q ⊠ R) {x = x ⊠ y} = cong₂ _⊠_ (μMor'Comp P Q) (μMor'Comp P R)
μMor'Comp P (Q ⊞ R) {x = ⊞₁ x} = cong ⊞₁ (μMor'Comp P Q)
μMor'Comp P (Q ⊞ R) {x = ⊞₂ x} = cong ⊞₂ (μMor'Comp P R)
μMor'Comp P (► Q) {x = ► x p} = cong₂-dep ► refl (funext (λ { [ j ] → funext (λ { [ k ] → refl }) }))
\end{code}

\begin{code}
μpsh : SemPoly tot → SemPoly tot → Ty tot
μpsh P Q = record
  { Obj = μObj' P Q
  ; Mor = μMor' P Q
  ; MorId = μMor'Id P Q
  ; MorComp = μMor'Comp P Q
  }
\end{code}

\begin{code}
mu : {Δ : tag} → (P : SemPoly Δ) → Ty Δ
mu {set} P = μset P P
mu {tot} P = μpsh P P
\end{code}
