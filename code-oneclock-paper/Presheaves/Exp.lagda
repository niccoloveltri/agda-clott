\AgdaHide{
\begin{code}
module Presheaves.Exp where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open PSh

module _ (P Q : PSh) where
\end{code}

  \begin{code}
  ExpObj : Size → Set
  ExpObj i =
    Σ[ f ∈ ((j : Size< (↑ i)) → Obj P j → Obj Q j) ]
      ((j : Size< (↑ i)) (k : Size< (↑ j)) (x : Obj P j)
        → Mor Q j k (f j x)
          ≡
          f k (Mor P j k x))
  \end{code}

  \begin{code}
  ExpMor : (i : Size) (j : Size< (↑ i))
    → ExpObj i → ExpObj j
  ExpMor i j (f , p) = f , p
  \end{code}

  \begin{code}
  ExpMorId : {i : Size} {x : ExpObj i}
    → ExpMor i i x ≡ x
  ExpMorId = refl
  \end{code}
  
  \begin{code}
  ExpMorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)}
    → {x : ExpObj i}
    → ExpMor i k x ≡ ExpMor j k (ExpMor i j x)
  ExpMorComp = refl
  \end{code}
}

Lastly, we need the exponential of presheaves.
For this, we use the standard construction of exponential objects in presheaf categories.

\begin{code}
Exp : PSh → PSh → PSh
\end{code}

\AgdaHide{
\begin{code}
Exp P Q = record
  { Obj = ExpObj P Q
  ; Mor = ExpMor P Q
  ; MorId = ExpMorId P Q
  ; MorComp = ExpMorComp P Q
  }
\end{code}
}
