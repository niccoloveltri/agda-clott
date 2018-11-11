{-
Weakening of clock contexts.
From A : Ty n and a Name i we can make a type in Ty (S n).
We do this by leaving a position open, so we need i : Name (suc n).
-}
module CloTT.TypeFormers.WeakenClock where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure

module _ (A : Ty set) where

  -- Object part
  WCObj : Size → Set
  WCObj _ = A

  -- Morphism part
  WCMor : (i : Size) (j : Size≤ i)
    → WCObj i → WCObj j
  WCMor _ _ x = x

  -- Preservation of identity
  WCMorId : {i : Size} {x : WCObj i}
    → WCMor i i x ≡ x
  WCMorId = refl

  -- Preservation of identity
  WCMorComp : {i : Size} {j : Size≤ i} {k : Size≤ j}
    {x : WCObj i}
    → WCMor i k x ≡ WCMor j k (WCMor i j x)
  WCMorComp = refl

  WC : Ty tot
  WC = record
    { Obj = WCObj
    ; Mor = WCMor
    ; MorId = WCMorId
    ; MorComp = WCMorComp
    }

-- functoriality

WC-fun : (Γ : Ctx set) (A : Ty set) → Tm set Γ A → Tm tot (WC Γ) (WC A)
proj₁ (WC-fun Γ A t) _ = t
proj₂ (WC-fun Γ A t) _ _ _ = refl

WC-unfun : (Γ : Ctx set) (A : Ty set) → Tm tot (WC Γ) (WC A) → Tm set Γ A 
WC-unfun Γ A (t , p) = t ∞
