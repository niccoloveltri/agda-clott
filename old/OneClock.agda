module OneClock where

open import Size
open import Level
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product


{- Clocked Type Theory in Agda via sized types -}

-- In this file we consider clock contexts containing only one
-- clock. This is just to set things right before generalizing to
-- multiple clocks.

-- A clock is a size. A tick on a clock κ is a size smaller than κ.

Clock = Size

Tick : Clock → Set
Tick κ = Size< κ

-- A context (or a closed type) is a presheaf over clocks. Notice
-- though that clocks form a preorder, not a poset.
-- Perhaps there should also be a field:
--    next-ass : {κ : Clock}{α : Tick κ}{β : Tick α}
--      → (γ : Γ κ) → next {α}{β} (next γ) ≡ next {κ}{β} γ


record Ctx ℓ : Set (Level.suc ℓ) where
  constructor ctx
  field
    Γ : Clock → Set ℓ
    next : {κ : Clock}{α : Tick κ} → Γ κ → Γ α
open Ctx

ClTy = Ctx

-- The later modality. The type ⊳ A κ looks like a dependent function
-- space, as in CloTT.

record ⊳ {ℓ} (A : Clock → Set ℓ) (κ : Clock) : Set ℓ where 
  coinductive
  constructor later
  field force : {α : Tick κ} → A α
open ⊳

-- Functoriality of ⊳. So ⊳ lifts to an operation on contexts.

⊳-next : ∀{ℓ} (A : Clock → Set ℓ) {κ : Clock} {α : Tick κ} → ⊳ A κ → ⊳ A α
⊳-next A x = x

⊳-Ctx :  ∀{ℓ} → Ctx ℓ → Ctx ℓ
⊳-Ctx (ctx Γ _) = ctx (⊳ Γ) (⊳-next Γ) 

-- Dependent types. As usual in presheaf semantics, a type in a
-- context Γ is a presheaf on the category og elements of Γ.

record Ty ℓ (c : Ctx ℓ) : Set (Level.suc ℓ) where
  constructor ty
  field
    A : (κ : Clock) → Γ c κ → Set ℓ
    Ty-next : {κ : Clock}{α : Tick κ}(γ : Γ c κ) → A κ γ → A α (next c γ)
open Ty

-- Pi types.

∏ : ∀ {ℓ} (A : Clock → Set ℓ) (B : (κ : Clock) → A κ → Set ℓ) → Clock → Set ℓ
∏ A B κ = {α : Tick κ} → (x : A α) → B α x

∏-next : ∀ {ℓ} (A : Clock → Set ℓ) (B : (κ : Clock) → A κ → Set ℓ)
  → {κ : Clock} {α : Tick κ} → ∏ A B κ → ∏ A B α
∏-next A B f x = f x

∏-Ty : ∀ {ℓ} (c : ClTy ℓ) (t : Ty ℓ c) → ClTy ℓ
∏-Ty (ctx Γ _) (ty A _) = ctx (∏ Γ A) (∏-next Γ A)
  

-- Sigma types.

∑ : ∀ {ℓ} (A : Clock → Set ℓ) (B : (κ : Clock) → A κ → Set ℓ) → Clock → Set ℓ
∑ A B κ = Σ (A κ) (B κ)

∑-next : ∀ {ℓ} (c : Ctx ℓ) (t : Ty ℓ c)
  → {κ : Clock} {α : Tick κ} → ∑ (Γ c) (A t) κ → ∑ (Γ c) (A t) α
∑-next (ctx Γ nΓ) (ty A nA) (γ , a) = nΓ γ , nA γ a


-- Dependent later modality.

record ⊳-dep {ℓ} {Γ : Clock → Set ℓ}
                 (A : (κ : Clock) → Γ κ → Set ℓ)
                 (κ : Clock) (γ : ⊳ Γ κ) : Set ℓ where
  coinductive
  field force : {α : Tick κ} → A α (force γ)
open ⊳-dep


⊳-dep-next : ∀{ℓ} {Γ : Clock → Set ℓ} (A : (κ : Clock) → Γ κ → Set ℓ)
  → {κ : Clock} {α : Tick κ} (γ : ⊳ Γ κ)
  → ⊳-dep A κ γ
  → ⊳-dep A α (⊳-next Γ γ)
force (⊳-dep-next A γ a) = force a  

⊳-Ty :  ∀{ℓ}(c : Ctx ℓ) → Ty ℓ c → Ty ℓ (⊳-Ctx c)
⊳-Ty (ctx Γ _) (ty A _) = ty (⊳-dep A) (⊳-dep-next A)


-- ⊳ is an applicative functor

infixl 30 _⊛_

_⊛_ : ∀ {ℓ} {Γ : Clock → Set ℓ} {A : (κ : Clock) → Γ κ → Set ℓ}
  → {κ : Clock} → ⊳ (∏ Γ A) κ → ∏ (⊳ Γ) (⊳-dep A) κ
force (f ⊛ x) = force f (force x)


-- Equality for ⊳ A.
-- We have to postulate extensional equality for the later modality. I
-- am not completely sure this is correct... Should this be defined
-- only on ⊳ A ∞ ? That's how it is done in the literature (Abel
-- papers) for other coinductive types.

record _⊳[_]≡_ {ℓ} {A : Clock → Set ℓ} {κ : Clock} (x : ⊳ A κ) (κ' : Clock) (y : ⊳ A κ) : Set ℓ where 
  coinductive
  field force-eq : {α : Tick κ'} → force x ≡ force y
open _⊳[_]≡_

postulate
  ⊳≡ : ∀ {ℓ} {A : Clock → Set ℓ} {κ : Clock} {x y : ⊳ A κ} → x ⊳[ ∞ ]≡ y → x ≡ y
