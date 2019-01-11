\AgdaHide{
\begin{code}
module CloTT.TypeFormers.Later where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure

open PSh
\end{code}
}

The first type constructor we discuss, is later.
Intuitively, inhabitants of $\blacktriangleright$ \AB{A} are inhabitants of \AB{A}, but available one time step from now.
For this reason, the main ingredient of defining the later modality is blocking computations.
This is done in several steps and first we define a type \AD{SizeLt}

\begin{code}
data SizeLt (i : Size) : Set where
  [_] : (j : Size< i) → SizeLt i
\end{code}

Functions on \AD{Size<} are defined using $\lambda$-abstraction.
This means that, whenever it has an input, it can apply $\beta$-elimination to unfold.
However, for \AD{SizeLt}, one can also use pattern matching.
In this case, the definition can only be unfolded after inspecting the element, and that blocks the computation.
This is essential for defining guarded recursion.

From an inhabitant of \AD{SizeLt}, we can obtain an actual size.
Note that this size is only available when we know it is of the shape \IC{[} \AB{j} \IC{]}.

\begin{code}
size : ∀ {i} → SizeLt i → Size
size [ j ] = j

size< : ∀ {i} → SizeLt i → Size< i
size< [ j ] = j
\end{code}

The type ▻ \AB{A} is also defined as a limit.
On each coordinate \AB{i}, we take the limit of \AB{A} restricted to the sizes smaller than \AB{i}.
Again we use a $\Sigma$-type for the definition.
The first component is represented by the type \F{Later}.

\begin{code}
Later : (Size → Set) → Size → Set
Later A i = (j : SizeLt i) → A (size j)
\end{code}

The second component is more difficult.
Usually, one would expect a universally quantified equality.
To make everything work with \AD{SizeLt}, we need an intermediate definition.

\begin{code}
elimLt : {A : Size → Set₁} {i : Size} → ((j : Size< i) → A j)
  → (j : SizeLt i) → A (size j)
elimLt f [ j ] = f j
\end{code}

This function does pattern matching on \F{SizeLt} and we use it to build predicate on \AD{SizeLt}.
Rather than using an element from \AD{SizeLt}, we put an element from \AD{Size<} into this predicate.
We can thus define the type of the second component as follows.

\AgdaHide{
\begin{code}
module _ (A : Size → Set) (m : (i : Size) (j : Size< (↑ i)) → A i → A j)  where
\end{code}
}

\begin{code}
  LaterLim : (i : Size) (x : Later A i) → Set
  LaterLim i x = (j : SizeLt i)
    → elimLt (λ { j' → (k : SizeLt (↑ j'))
      → elimLt (λ k' → m j' k' (x [ j' ]) ≡ x [ k' ]) k }) j
\end{code}

\AgdaHide{
\begin{code}
  LaterLimMor : (i : Size) (j : Size< (↑ i)) (x : Later A i)
    → LaterLim i x → LaterLim j x
  LaterLimMor i j x p [ k ] [ l ] = p [ k ] [ l ] -- p [ k ]

module _ (A : Ty tot) where
\end{code}
}

Now we put it all together and we obtain the following definition of the object part.
In addition, we can define an action on the morphisms and show this preserves identity and composition.
All in all, we get

\begin{code}
  ▻Obj : (i : Size) → Set
  ▻Obj i = Σ (Later (Obj A) i) (LaterLim (Obj A) (Mor A) i)
\end{code}

\AgdaHide{
\begin{code}
  ▻Mor : (i : Size) (j : Size< (↑ i))
    → ▻Obj i → ▻Obj j
  ▻Mor i j (x , p) = x , LaterLimMor (Obj A) (Mor A) i j x p

  ▻MorId : {i : Size} {x : ▻Obj i}
             → ▻Mor i i x ≡ x
  ▻MorId = Σ≡-uip (funext (λ { [ j ] → funext (λ { [ k ] → uip }) })) refl

  ▻MorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)} {x : ▻Obj i}
               → ▻Mor i k x ≡ ▻Mor j k (▻Mor i j x)
  ▻MorComp = Σ≡-uip (funext (λ { [ j ] → funext (λ { [ k ] → uip }) })) refl
\end{code}
}

\begin{code}
▻ : Ty tot → Ty tot
\end{code}

\AgdaHide{
\begin{code}
▻ A = record
    { Obj = ▻Obj A
    ; Mor = ▻Mor A
    ; MorId = ▻MorId A
    ; MorComp = ▻MorComp A
    }
\end{code}
}
