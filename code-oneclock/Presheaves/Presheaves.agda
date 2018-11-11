{-
In this file, we define the notion of presheaves.
For each n : ℕ, we define presheaves on the site ClockCtx n.
The objects of this sites, are n-tuples of sizes.
This is a preorder since Size is a preorder.
-}
module Presheaves.Presheaves where

open import Prelude

record PSh : Set₁ where
  field
    -- Object part
    Obj : Size → Set
    -- Morphism part
    Mor : (i : Size) (j : Size≤ i)
      → Obj i → Obj j
    -- Preservation of identity
    MorId : {i : Size} {x : Obj i}
      → Mor i i x ≡ x
    -- Preservation of composition
    MorComp : {i : Size} {j : Size≤ i} {k : Size≤ j}
      → {x : Obj i}
      → Mor i k x ≡ Mor j k (Mor i j x)


