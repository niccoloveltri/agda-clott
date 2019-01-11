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

From an inhabitant of \AD{SizeLt}, we can obtain an actual size.
Note that this size is only available when we know it is of the shape \IC{[} \AB{j} \IC{]}.

\begin{code}
size : ∀ {i} → SizeLt i → Size
size [ j ] = j
\end{code}

The type $\blacktriangleright$ \AB{A} is also defined in several steps.
In each step, we take more structure of the presheaf \AB{A} into account.

Given a family of types over sizes, we can define later as follows.

\begin{code}
Later : (Size → Set) → Size → Set
Later A i = (j : SizeLt i) → A (size j)
\end{code}

However, this it not yet sufficient.
Note that types are presheaves and not just families of sizes.

\begin{code}
elimLt : ∀{ℓ} {A : Size → Set ℓ} {i : Size} (j : SizeLt i)
  → ((j : Size< i) → A j) → A (size j)
elimLt [ j ] f = f j
\end{code}

\AgdaHide{
\begin{code}
module _ (A : Size → Set) (m : (i : Size) (j : Size< (↑ i)) → A i → A j)  where
\end{code}
}

\begin{code}
  LaterLim : (i : Size) (x : Later A i) → Set
  LaterLim i x = (j : SizeLt i)
    → elimLt j (λ { j' → (k : SizeLt (↑ j'))
      → elimLt k (λ k' → m j' k' (x [ j' ]) ≡ x [ k' ]) })
\end{code}

\AgdaHide{
\begin{code}
  LaterLimMor : (i : Size) (j : Size< (↑ i)) (x : Later A i)
    → LaterLim i x → LaterLim j x
  LaterLimMor i j x p [ k ] = p [ k ]

module _ (A : Ty tot) where
\end{code}
}

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

We can also define an action on the morphisms and show this preserves identity and composition.
All in all, we get

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
