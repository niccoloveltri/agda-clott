{-
A context is a presheaf.
-}
module CloTT.Structure.Contexts where

open import Prelude
open import Presheaves public

Ctx : Bool → Set₁
Ctx set = Set
Ctx tot = PSh

