{-
The terminal presheaf.
It is defined as the constant presheaf which is the unit type on each coordinate.
-}
module Presheaves.Terminal where

open import Data.Unit
open import Prelude
open import Presheaves.Const 
open import Presheaves.Presheaves

Terminal : {n : ℕ} → PSh n
Terminal = Const ⊤
