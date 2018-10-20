{-
In this file, we define the notion of presheaves.
For each n : ℕ, we define presheaves on the site ClockCtx n.
The objects of this sites, are n-tuples of sizes.
This is a preorder since Size is a preorder.
-}
module Presheaves.Presheaves where

open import Prelude

record PSh (n : ℕ) : Set₁ where
  field
    -- Object part
    Obj : (Δ : ClockCtx n) → Set
    -- Morphism part
    Mor : (Δ : ClockCtx n)(Δ' : ClockCtx≤ Δ)
      → Obj Δ → Obj Δ'
    -- Preservation of identity
    MorId : {Δ : ClockCtx n} {x : Obj Δ}
      → Mor Δ (coeClockCtx Δ) x ≡ x
    -- Preservation of composition
    MorComp : {Δ : ClockCtx n}{Δ' : ClockCtx≤ Δ}
      → {Δ'' : ClockCtx≤ Δ'}{x : Obj Δ}
      → Mor Δ _ x ≡ Mor Δ' Δ'' (Mor Δ Δ' x)


