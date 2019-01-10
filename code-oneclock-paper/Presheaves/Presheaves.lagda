\AgdaHide{
\begin{code}
module Presheaves.Presheaves where

open import Prelude
\end{code}
}

Recall that the topos of trees consists presheaves on the first ordinal $\omega$.
We take a slightly different approach: we use presheaves on Agda's built-in type \AD{Size} instead.
Note that sizes indeed form a category, since they are partially ordered.

Presheaves are defined as a record \AD{PSh}.
Each field represents a part of the data.
The fields \AFi{Obj} and \AFi{Mor} represent the actions on objects and morphisms respectively.
There also are two laws, \AFi{MorId} and \AFi{MorComp}, which represent the functor laws.
\begin{code}
record PSh : Set₁ where
  field
    Obj : Size → Set
    Mor : (i : Size) (j : Size< (↑ i))
      → Obj i → Obj j
    MorId : {i : Size} {x : Obj i}
      → Mor i i x ≡ x
    MorComp : {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)}
      → {x : Obj i}
      → Mor i k x ≡ Mor j k (Mor i j x)
\end{code}
