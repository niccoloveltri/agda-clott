\AgdaHide{
\begin{code}
module Presheaves.Exp where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves

module _ (P Q : PSh) where
  open PSh
\end{code}
}

  \begin{code}
  ExpObj : Size → Set
  ExpObj i =
    Σ ((j : Size< (↑ i)) → Obj P j → Obj Q j)
      (λ f → (j : Size< (↑ i)) (k : Size< (↑ j))
             (x : Obj P j)
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

  \begin{code}
  Exp : PSh
  Exp = record
    { Obj = ExpObj
    ; Mor = ExpMor
    ; MorId = ExpMorId
    ; MorComp = ExpMorComp
    }
  \end{code}
