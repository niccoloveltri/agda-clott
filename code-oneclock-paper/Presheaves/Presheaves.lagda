\AgdaHide{
\begin{code}
module Presheaves.Presheaves where

open import Prelude
\end{code}
}

The objects of the topos of trees are presheaves on the first ordinal $\omega$.
We take a slightly different approach: rather than using $\omega$, we use Agda's built-in type \AD{Size}.
Since sizes are partially ordered, they form a category.

Presheaves are defined as a record.
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
We have a field \AFi{Obj}, which represents the action on objects.
The field \AFi{Mor} represents the action on morphisms.
Lastly, we have two laws, \AFi{MorId} and \AFi{MorComp}, which represent the functor laws.
