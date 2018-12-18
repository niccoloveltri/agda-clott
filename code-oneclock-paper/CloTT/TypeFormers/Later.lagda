\AgdaHide{
\begin{code}
module CloTT.TypeFormers.Later where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
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

\begin{code}
module _ (A : Size → Set) (m : (i : Size) (j : Size< (↑ i)) → A i → A j)  where

  LaterLim : (i : Size) (x : Later A i) → Set
  LaterLim i x = (j : SizeLt i)
    → elimLt j (λ { j' → (k : SizeLt (↑ j'))
      → elimLt k (λ k' → m j' k' (x [ j' ]) ≡ x [ k' ]) })

  LaterLimMor : (i : Size) (j : Size< (↑ i)) (x : Later A i)
    → LaterLim i x → LaterLim j x
  LaterLimMor i j x p [ k ] [ l ] = p [ k ] [ l ]
  
module _ (A : Ty tot) where

  -- 3. Object part
  ▻Obj : (i : Size) → Set
  ▻Obj i = Σ (Later (PSh.Obj A) i) (LaterLim (PSh.Obj A) (PSh.Mor A) i)

  -- 4. Morphism part
  ▻Mor : (i : Size) (j : Size< (↑ i))
    → ▻Obj i → ▻Obj j
  ▻Mor i j (x , p) = x , LaterLimMor (PSh.Obj A) (PSh.Mor A) i j x p
    where
      p' : LaterLim (PSh.Obj A) (PSh.Mor A) j x
      p' [ j ] [ k ] = p [ j ] [ k ]

  -- 5. Preservation of identity
  ▻MorId : {i : Size} {x : ▻Obj i}
             → ▻Mor i i x ≡ x
  ▻MorId = Σ≡-uip (funext (λ { [ j ] → funext (λ { [ k ] → uip }) })) refl

  -- 6. Preservation of composition
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
