{-
A type is a presheaf
-}
module CloTT.Structure.Types where

open import Prelude
open import Presheaves public

Ty : Bool → Set₁
Ty set = Set
Ty tot = PSh


