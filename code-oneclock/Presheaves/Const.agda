{-
The constant presheaf on A is A on each object and on each morphism the identity.
-}
module Presheaves.Const where

open import Prelude
open import Presheaves.Presheaves

module _ (A : Set) where

  -- Object part
  ConstObj : Size → Set
  ConstObj _ = A

  -- Morphism part
  ConstMor : (i : Size) (j : Size≤ i)
    → ConstObj i → ConstObj j
  ConstMor _ _ x = x

  -- Preservation of identity
  ConstMorId : {i : Size} {x : A}
    → ConstMor i i x ≡ x
  ConstMorId = refl

  -- Preservation of composition
  ConstMorComp : {i : Size} {j : Size≤ i} {k : Size≤ j}
    → {x : ConstObj i}
    → ConstMor i k x ≡ ConstMor j k (ConstMor i j x)
  ConstMorComp = refl
  
  Const : PSh set
  Const = record
    { Obj = ConstObj
    ; Mor = ConstMor
    ; MorId = ConstMorId
    ; MorComp = ConstMorComp
    }
