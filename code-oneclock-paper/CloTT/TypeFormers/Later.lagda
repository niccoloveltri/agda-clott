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

\begin{code}
data SizeLt (i : Size) : Set where
  [_] : (j : Size< i) → SizeLt i

size : ∀ {i} → SizeLt i → Size
size [ j ] = j
\end{code}

\begin{code}
elimLt : ∀{ℓ} {A : Size → Set ℓ} {i : Size} (j : SizeLt i)
  → ((j : Size< i) → A j) → A (size j)
elimLt [ j ] f = f j
\end{code}

\begin{code}
Later : (Size → Set) → Size → Set
Later A i = (j : SizeLt i) → A (size j)
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

  ▻ : Ty tot
  ▻ = record
    { Obj = ▻Obj
    ; Mor = ▻Mor
    ; MorId = ▻MorId
    ; MorComp = ▻MorComp
    }
\end{code}
}
