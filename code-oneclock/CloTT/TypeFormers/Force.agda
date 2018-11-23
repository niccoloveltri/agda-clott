module CloTT.TypeFormers.Force where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.ClockQuantification

force-tm : (Γ : Ctx set) (A : Ty tot) (t : Tm set Γ (□ (▻ A))) → Tm set Γ (□ A)
proj₁ (force-tm Γ A t x) j = proj₁ (proj₁ (t x) ∞) [ j ]
proj₂ (force-tm Γ A t x) i j = proj₂ (proj₁ (t x) ∞) [ i ] [ j ]

