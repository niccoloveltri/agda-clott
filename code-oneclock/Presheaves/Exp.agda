{-
The exponential in the presheaf category.
-}
module Presheaves.Exp where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves

module _ (P Q : PSh) where

  private module P = PSh P
  private module Q = PSh Q

  -- Object part
  ExpObj : Size → Set
  ExpObj i =
    Σ ((j : Size≤ i) → P.Obj j → Q.Obj j)
      (λ f → (j : Size≤ i) (k : Size≤ j)
             (x : P.Obj j)
               → Q.Mor j k (f j x)
                 ≡
                 f k (P.Mor j k x))

  -- Morphism part
  ExpMor : (i : Size) (j : Size≤ i)
    → ExpObj i → ExpObj j
  ExpMor i j (f , p) = (λ _ → f _) , (λ _ _ → p _ _)

  -- Presevation of identity
  ExpMorId : {i : Size} {x : ExpObj i}
    → ExpMor i i x ≡ x
  ExpMorId = refl

  -- Preservation of composition
  ExpMorComp : {i : Size} {j : Size≤ i} {k : Size≤ j}
    → {x : ExpObj i}
    → ExpMor i k x ≡ ExpMor j k (ExpMor i j x)
  ExpMorComp = refl

  Exp : PSh
  Exp = record
    { Obj = ExpObj
    ; Mor = ExpMor
    ; MorId = ExpMorId
    ; MorComp = ExpMorComp
    }

