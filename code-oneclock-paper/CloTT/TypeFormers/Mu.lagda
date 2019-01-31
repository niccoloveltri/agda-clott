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
To define guarded recursive types, we define the semantics of polynomials.
The reason why we cannot use the syntactic ones, is because the constant polynomial should depend on \AD{SemTy} rather than \AD{Ty}.
This leads to the following definition.

\begin{code}
data SemPoly : ClockCtx → Set₁ where
    ∁ : ∀ {Δ} → SemTy Δ → SemPoly Δ
    I : ∀ {Δ} → SemPoly Δ
    _⊞_ _⊠_ : ∀ {Δ} → SemPoly Δ → SemPoly Δ → SemPoly Δ
    ▸ : SemPoly κ → SemPoly κ
\end{code}
\AgdaHide{
Again we can evaluate polynomials as endofunctors on \F{SemTy} \AB{Δ}.
\begin{code}
sem-eval : ∀ {Δ} → SemPoly Δ → SemTy Δ → SemTy Δ
sem-eval (∁ A) X = A
sem-eval I X = X
sem-eval (P ⊞ Q) X = sem-eval P X ⊕ sem-eval Q X
sem-eval (P ⊠ Q) X = sem-eval P X ⊗ sem-eval Q X
sem-eval (▸ P) X = ►(sem-eval P X)
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

In the remainder of this section, we only consider guarded recursive types in the clock context \AIC{κ}.
Those in \AIC{∅} are interpreted similarly.
Given a polynomial \AB{P}, we must define the object and morphism part of a presheaf \F{μpsh} \AB{P}.
Since both parts are defined with a similar technique, we only explain how to define the object part \F{μObj} \AB{P}.

A first attempt to define \F{μObj} \AB{P}, would be using induction on \AB{P}.
However, there is a problem when we arrive at the identity polynomial.
In that case, a recursive call is made, so we need to refer back to original polynomial \AB{P}, which is unavailable at this point.
To solve that, we use a trick: we define a data type \F{μObj'}, which depends on two polynomials instead of one.
The first polynomial is the polynomial used to define the guarded recursive type and we do induction on the second one.
In the end, we define \F{μObj} \AB{P} to be \F{μObj'} \AB{P} \AB{P}.

The data type \F{μObj'} \AB{P} \AB{Q} is defined as an inductive type.
The constructors say how to construct inhabitans depending on whether \AB{Q} is constant, a product, a sum, \etc.
If \AB{Q} is a product or sum, they are pairs or injections respectively.
For the identity, we need to use \AB{P} to make a recursive call.

However, the main difficulty is \AIC{►P}.
This is because the later modality depends on both the object and morphism part of its argument.
For this reason, we need to define \F{μObj'} and \F{μMor'} mutually.
We define them formally as follows.

\begin{code}
  data μObj' (P : SemPoly κ) : SemPoly κ → Size → Set where
    ∁ps   : {X : PSh} {i : Size} → Obj X i → μObj' P (∁ X) i
    I     : ∀{i} → μObj' P P i → μObj' P I i
    _⊠_  : ∀{Q R i} → μObj' P Q i → μObj' P R i → μObj' P (Q ⊠ R) i
    ⊞₁   : ∀{Q R i} → μObj' P Q i → μObj' P (Q ⊞ R) i
    ⊞₂   : ∀{Q R i} → μObj' P R i → μObj' P (Q ⊞ R) i
    ►P    : ∀{Q i} (x : Later (μObj' P Q) i)
      → LaterLim (μObj' P Q) (μMor' P Q) i x → μObj' P (▸ Q) i
\end{code}

\begin{code}
  μMor' : (P Q : SemPoly κ) (i : Size) (j : Size< (↑ i))
    → μObj' P Q i → μObj' P Q j
  μMor' P (∁ X) i j (∁ps x)        = ∁ps (Mor X i j x)
  μMor' P I i j (I x)              = I (μMor' P P i j x)
  μMor' P (Q ⊠ R) i j (x ⊠ y)     = μMor' P Q i j x ⊠ μMor' P R i j y
  μMor' P (Q ⊞ R) i j (⊞₁ x)      = ⊞₁ (μMor' P Q i j x)
  μMor' P (Q ⊞ R) i j (⊞₂ x)      = ⊞₂ (μMor' P R i j x)
  μMor' P (▸ Q) i j (►P x p)      = ►P x q
    where
      q : LaterLim (μObj' P Q) (μMor' P Q) j x
      q [ k ] [ l ] = p [ k ] [ l ]
\end{code}

\remove{
We define the object part and the morphism part mutually.
Usually, the morphism part depends on the object part, but not the other way around.
Since \F{►} \AB{A} is defined as a limit, it depends on both the object and the morphism part of \AB{A}.
Hence, to define the action of \AIC{►P} on the objecs, both parts are needed, and thus \F{μObj'} and \F{μMor'} are defined mutually.

\To define the elements of \AIC{μ} \AB{P}, we use an intermediate step.
We define a type family \AD{μObj'}, which does not just depend on \AB{P}, but also on a second polynomial \AB{Q}.
In the end, we take the object part of \AIC{μ} \AB{P} to be \AD{μobj} \AB{P} \AB{P} and similar for the morphisms.
This allows us to do induction on \AB{Q} while remembering \AB{P}.

For the product, sum, and constant polynomial, it is straightforward to define the elements.
For later, we use \F{LaterLim} as defined before.
The identity case, on the other hand, requires more thinking.
The input then is something from the presheaf \AIC{μ} \AB{P} of which the object map is \AD{μobj} \AB{P} \AB{P}.
If we were using induction and we arrived at the identity polynomial, we are unable to get the original polynomial.
For that reason, we must keep track of the original polynomial, which is the argument \Ar{P}.
The morphism part \AD{μMor'} also depends on two polynomials and it is defined by induction.
}

\AgdaHide{
\begin{code}
μMor'Id : (P Q : SemPoly κ) {i : Size} {x : μObj' P Q i} → μMor' P Q i i x ≡ x
μMor'Id P (∁ X) {i} {∁ps x} = cong ∁ps (MorId X)
μMor'Id P I {i}{I x} = cong I (μMor'Id P P)
μMor'Id P (Q ⊠ R) {i}{x ⊠ y} = cong₂ _⊠_ (μMor'Id P Q) (μMor'Id P R)
μMor'Id P (Q ⊞ R) {i}{⊞₁ x} = cong ⊞₁ (μMor'Id P Q)
μMor'Id P (Q ⊞ R) {i}{⊞₂ x} = cong ⊞₂ (μMor'Id P R)
μMor'Id P (▸ Q) {i}{►P x p} = cong₂-dep ►P refl (funext (λ { [ j ] → funext (λ { [ k ] → refl }) }))
\end{code}

\begin{code}
μMor'Comp : (P Q : SemPoly κ) {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)} {x : μObj' P Q i}
  → μMor' P Q i k x ≡ μMor' P Q j k (μMor' P Q i j x)
μMor'Comp P (∁ X) {x = ∁ps x} = cong ∁ps (MorComp X)
μMor'Comp P I {x = I x} = cong I (μMor'Comp P P)
μMor'Comp P (Q ⊠ R) {x = x ⊠ y} = cong₂ _⊠_ (μMor'Comp P Q) (μMor'Comp P R)
μMor'Comp P (Q ⊞ R) {x = ⊞₁ x} = cong ⊞₁ (μMor'Comp P Q)
μMor'Comp P (Q ⊞ R) {x = ⊞₂ x} = cong ⊞₂ (μMor'Comp P R)
μMor'Comp P (▸ Q) {x = ►P x p} = cong₂-dep ►P refl (funext (λ { [ j ] → funext (λ { [ k ] → refl }) }))
\end{code}
}

Since \AD{μMor'} preserves the identity and composition, we get a presheaf \AD{μpsh}.
\begin{code}
μpsh : SemPoly κ → SemPoly κ → SemTy κ
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
The presheaf \AD{μpsh} \AB{P} \AB{P} gives the interpretation for \AIC{μ} in the clock context \AIC{κ}.

\AgdaHide{
\begin{code}
mu : ∀ {Δ} → (P : SemPoly Δ) → SemTy Δ
mu {κ} P = μpsh P P
\end{code}
}

\AgdaHide{
\begin{code}
mu {∅} P = μset P P
\end{code}
}
