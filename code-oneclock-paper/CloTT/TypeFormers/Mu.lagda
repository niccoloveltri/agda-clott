\AgdaHide{
\begin{code}
module CloTT.TypeFormers.Mu where

open import Data.Sum renaming (map to map⊎)
open import Data.Product renaming (map to map×)
open import Prelude
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
To define guarded recursive types, we first need to define the semantics of polynomials.
The reason why we cannot use the syntactic ones, is because we need to use inhabitants of \AD{Ty} in the constant polynomial.
This leads to the following definition.

\begin{code}
data SemPoly : ClockContext → Set₁ where
    ∁ : ∀ {Δ} → Ty Δ → SemPoly Δ
    I : {Δ : ClockContext} → SemPoly Δ
    _⊞_ _⊠_ : {Δ : ClockContext} → SemPoly Δ → SemPoly Δ → SemPoly Δ
    ►P : SemPoly κ → SemPoly κ
\end{code}

Note that we can evaluate polynomials into functors on types.
This is defined by induction on the polynomial.
In each case, we use the corresponding opertion on types.

\begin{code}
eval : {Δ : ClockContext} → SemPoly Δ → Ty Δ → Ty Δ
\end{code}

\AgdaHide{
\begin{code}
eval (∁ A) X = A
eval I X = X
eval (P ⊞ Q) X = eval P X ⊕ eval Q X
eval (P ⊠ Q) X = eval P X ⊗ eval Q X
eval (►P P) X = ►(eval P X)
\end{code}
}

\AgdaHide{
\begin{code}
data μset (P : SemPoly ∅) : SemPoly ∅ → Set where
  ∁s : {X : Set} → X → μset P (∁ X)
  I : μset P P → μset P I
  _⊠_ : {Q R : SemPoly ∅} → μset P Q → μset P R → μset P (Q ⊠ R)
  ⊞₁ : {Q R : SemPoly ∅} → μset P Q → μset P (Q ⊞ R)
  ⊞₂ : {Q R : SemPoly ∅} → μset P R → μset P (Q ⊞ R)
\end{code}
}

\AgdaHide{
\begin{code}
mutual
\end{code}
}

In the remainder of this section, we focus on μ-types in the clock context with a single clock variable.
We define the object part and the morphism part mutually.
Usually, the morphism part depends on the object part, but not the other way around.
Since ► \AB{A} is defined as a limit, it uses both the object and the morphism part of \AB{A}.
Hence, in case of \AIC{►P}, both parts are needed, and thus \F{μObj'} and \F{μMor'} are defined mutually.

For each polynomial \AB{P}, we indicate how to construct elements of \F{μ} \AB{P}.
The constructors for this are in the data type \AD{μObj'}.
The morphism part \AD{μMor'} is defined by induction.

The type family \AD{μObj'} does not just depend on \AB{P}, but also on a second polynomial \AB{Q}.
In the end, we take the object part of \AD{μ} \AB{P} to be \AD{μobj} \AB{P} \AB{P} and similar for the morphisms.
This allows to induction on \AB{Q} while remembering \AB{P}.

Most cases are straightforward.
For the sum, we can use both inclusions, for the product, we use pairing, and so on.
For later, we use \F{LaterLim} as defined before.
The identity case goes differently.
The input then is something from the presheaf \AD{μ} \AB{P} of which the object map is \AD{μobj} \AB{P} \AB{P}.
If we were using induction and we arrived at the identity polynomial, we are unable to get the original polynomial.
For that reason, we must keep track of the original polynomial, which is added as an extra argument.
We use the same trick for \AD{μMor'}.


\begin{code}
  data μObj' (P : SemPoly κ) : SemPoly κ → Size → Set where
    ∁ps : {X : PSh} {i : Size} → Obj X i → μObj' P (∁ X) i
    I : ∀{i} → μObj' P P i → μObj' P I i
    _⊠_ : ∀{Q R i} → μObj' P Q i → μObj' P R i → μObj' P (Q ⊠ R) i
    ⊞₁ : ∀{Q R i} → μObj' P Q i → μObj' P (Q ⊞ R) i
    ⊞₂ : ∀{Q R i} → μObj' P R i → μObj' P (Q ⊞ R) i
    ►P : ∀{Q i} (x : Later (μObj' P Q) i)
      → LaterLim (μObj' P Q) (μMor' P Q) i x → μObj' P (►P Q) i
\end{code}

\begin{code}
  μMor' : (P Q : SemPoly κ) (i : Size) (j : Size< (↑ i))
    → μObj' P Q i → μObj' P Q j
  μMor' P (∁ X) i j (∁ps x)   = ∁ps (Mor X i j x)
  μMor' P I i j (I x)           = I (μMor' P P i j x)
  μMor' P (Q ⊠ R) i j (x ⊠ y)  = μMor' P Q i j x ⊠ μMor' P R i j y
  μMor' P (Q ⊞ R) i j (⊞₁ x)   = ⊞₁ (μMor' P Q i j x)
  μMor' P (Q ⊞ R) i j (⊞₂ x)   = ⊞₂ (μMor' P R i j x)
  μMor' P (►P Q) i j (►P x p)   = ►P x q
    where
      q : LaterLim (μObj' P Q) (μMor' P Q) j x
      q [ k ] [ l ] = p [ k ] [ l ]
\end{code}

\AgdaHide{
\begin{code}
μMor'Id : (P Q : SemPoly κ) {i : Size} {x : μObj' P Q i} → μMor' P Q i i x ≡ x
μMor'Id P (∁ X) {i} {∁ps x} = cong ∁ps (MorId X)
μMor'Id P I {i}{I x} = cong I (μMor'Id P P)
μMor'Id P (Q ⊠ R) {i}{x ⊠ y} = cong₂ _⊠_ (μMor'Id P Q) (μMor'Id P R)
μMor'Id P (Q ⊞ R) {i}{⊞₁ x} = cong ⊞₁ (μMor'Id P Q)
μMor'Id P (Q ⊞ R) {i}{⊞₂ x} = cong ⊞₂ (μMor'Id P R)
μMor'Id P (►P Q) {i}{►P x p} = cong₂-dep ►P refl (funext (λ { [ j ] → funext (λ { [ k ] → refl }) }))
\end{code}

\begin{code}
μMor'Comp : (P Q : SemPoly κ) {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)} {x : μObj' P Q i}
  → μMor' P Q i k x ≡ μMor' P Q j k (μMor' P Q i j x)
μMor'Comp P (∁ X) {x = ∁ps x} = cong ∁ps (MorComp X)
μMor'Comp P I {x = I x} = cong I (μMor'Comp P P)
μMor'Comp P (Q ⊠ R) {x = x ⊠ y} = cong₂ _⊠_ (μMor'Comp P Q) (μMor'Comp P R)
μMor'Comp P (Q ⊞ R) {x = ⊞₁ x} = cong ⊞₁ (μMor'Comp P Q)
μMor'Comp P (Q ⊞ R) {x = ⊞₂ x} = cong ⊞₂ (μMor'Comp P R)
μMor'Comp P (►P Q) {x = ►P x p} = cong₂-dep ►P refl (funext (λ { [ j ] → funext (λ { [ k ] → refl }) }))
\end{code}
}

In addition, we can show that \AD{μMor'} preserves the identity and composition and thus we get a presheaf \AD{μpsh}.

\begin{code}
μpsh : SemPoly κ → SemPoly κ → Ty κ
\end{code}

\AgdaHide{
\begin{code}
μpsh P Q = record
  { Obj = μObj' P Q
  ; Mor = μMor' P Q
  ; MorId = μMor'Id P Q
  ; MorComp = μMor'Comp P Q
  }
\end{code}
}

Finally, we define \AD{μ}.
We make a case distinction based on the clock context.
For presheaves, we \AD{μpsh} taking \AB{P} for both polynomials.

\begin{code}
mu : {Δ : ClockContext} → (P : SemPoly Δ) → Ty Δ
mu {κ} P = μpsh P P
\end{code}

\AgdaHide{
\begin{code}
mu {∅} P = μset P P
\end{code}
}
