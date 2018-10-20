{-
In this file, we define the notion of clock contexts.
A clock context is of the shape κ₁, ...., κn.
The names of these clocks are 1, ..., n.
In the presheaf category, we assign to each name a value.

A tick is a resource of a clock.
A lazy computation has a clock and to force this computation, one needs to give
a resource for this clock.
We use the mechanism of sized types to guarantee productivity.
For that reason, we define Tick using Size<.

The file is structured as follows
1. Coercions on size
2. Basic definitions
3. Category of clocks
4. Operations on clock contexts
5. Properties
-}
module Prelude.ClockContexts where

open import Prelude.Basics
open import Size
open import Data.Fin
open import Data.Empty
open import Data.Nat hiding (_≟_)
open import Data.Vec
open import Function
open import Data.Product
open import Data.Fin.Properties
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- 1. Coercions on size.
Size≤ : Size → Set
Size≤ i = Size< (↑ i)

coeSize : (i : Size) → Size≤ i
coeSize i = i

transSize≤ : {i : Size} {j : Size≤ i} → Size≤ j → Size≤ i
transSize≤ k = k

transSize<≤ : {i : Size} {j : Size< i} → Size≤ j → Size< i
transSize<≤ k = k

transSize≤< : {i : Size} {j : Size≤ i} → Size< j → Size< i
transSize≤< k = k

-- 2. Basic definitions.
Clock = Size

Name : ℕ → Set
Name n = Fin n

ClockCtx : ℕ → Set
ClockCtx n = Name n → Clock

Tick : Size → Set
Tick i = Size< i

TickCtx : {n : ℕ} → ClockCtx n → Name n → Set
TickCtx Δ j = Tick (Δ j)

-- 3. Category of clocks
ClockCtx< : {n : ℕ} → ClockCtx n → Set
ClockCtx< {n} Δ = Σ (Name n) (λ i → Size< (Δ i))

-- Arrows in the category of clocks
ClockCtx≤ : {n : ℕ} → ClockCtx n → Set
ClockCtx≤ {n} Δ = (i : Name n) → Size≤ (Δ i)

-- Identity arrow
coeClockCtx : {n : ℕ} (Δ : ClockCtx n) → ClockCtx≤ Δ
coeClockCtx Δ i = coeSize (Δ i)

-- Composition of arrows
transClockCtx≤ : {n : ℕ}
  → {Δ₁ : ClockCtx n} {Δ₂ : ClockCtx≤ Δ₁}
  → ClockCtx≤ Δ₂ → ClockCtx≤ Δ₁
transClockCtx≤ {Δ₁ = Δ₁} Δ₃ j = transSize≤ {Δ₁ j} (Δ₃ j)

-- 4. Operations on clock contexts
removeClock : ∀{n} → Name (suc n) → ClockCtx (suc n) → ClockCtx n
removeClock zero Δ j = Δ (suc j)
removeClock (suc i) Δ zero = Δ zero
removeClock (suc i) Δ (suc j) = removeClock i (Δ ∘ suc) j

_[_↦_] : {n : ℕ} → ClockCtx n → Name n → Clock → ClockCtx n
(Δ [ i ↦ κ ]) j with i ≟ j
(Δ [ i ↦ κ ]) .i | yes refl = κ
(Δ [ i ↦ κ ]) j | no ¬p = Δ j

_[_↦_]≤ : {n : ℕ} (Δ : ClockCtx n) (i : Name n)
  → Size≤ (Δ i) → ClockCtx≤ Δ
(Δ [ i ↦ κ ]≤) j with i ≟ j
(Δ [ i ↦ κ ]≤) .i | yes refl = κ
(Δ [ i ↦ κ ]≤) j | no ¬p = coeSize (Δ j)

id[↦] : {n : ℕ} {Δ : ClockCtx n} {i : Name n} {κ : Clock}
  → (Δ [ i ↦ κ ]) i ≡ κ
id[↦] {i = i} with i ≟ i
id[↦] {i = i} | yes refl = refl
id[↦] {i = i} | no q = ⊥-elim (q refl)

insertClockCtx : {n : ℕ} → Name (suc n) → Clock
  → ClockCtx n → ClockCtx (suc n)
insertClockCtx zero κ Δ zero = κ
insertClockCtx zero κ Δ (suc j) = Δ j
insertClockCtx {zero} (suc ()) κ Δ j
insertClockCtx {suc n} (suc i) κ Δ zero = Δ zero
insertClockCtx {suc n} (suc i) κ Δ (suc j) =
  insertClockCtx i κ (Δ ∘ suc) j

insertClockCtx≤ : {n : ℕ} (i : Name (suc n))
  → (κ : Clock) (α : Size≤ κ)
  → (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
  → ClockCtx≤ (insertClockCtx i κ Δ)
insertClockCtx≤ zero κ α Δ Δ' zero = α
insertClockCtx≤ zero κ α Δ Δ' (suc j) = Δ' j
insertClockCtx≤ {zero} (suc ()) κ α Δ Δ' j
insertClockCtx≤ {suc n} (suc i) κ α Δ Δ' zero = Δ' zero
insertClockCtx≤ {suc n} (suc i) κ α Δ Δ' (suc j) =
  insertClockCtx≤ i κ α (Δ ∘ suc) (λ k → Δ' (suc k)) j

-- 5. Operations
insertClockCtx-lem' : {n : ℕ} (i : Name (suc n))
  → (κ : Clock) (α : Size≤ κ)
  → (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
  → (j : Fin (suc n))
  → insertClockCtx i α Δ' j ≡ insertClockCtx≤ i κ α Δ Δ' j
insertClockCtx-lem' zero κ α Δ Δ' zero = refl
insertClockCtx-lem' zero κ α Δ Δ' (suc j) = refl
insertClockCtx-lem' {zero} (suc ()) κ α Δ Δ' j
insertClockCtx-lem' {suc n} (suc i) κ α Δ Δ' zero = refl
insertClockCtx-lem' {suc n} (suc i) κ α Δ Δ' (suc j) =
  insertClockCtx-lem' i κ α (Δ ∘ suc) (λ k → Δ' (suc k)) j

insertClockCtx-lem : {n : ℕ} (i : Name (suc n))
  → (κ : Clock) (α : Size≤ κ)
  → (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
  → insertClockCtx i α Δ' ≡ insertClockCtx≤ i κ α Δ Δ'
insertClockCtx-lem i κ α Δ Δ' =
  funext (insertClockCtx-lem' i κ α Δ Δ')

remove-insert' : {n : ℕ} {Δ : ClockCtx n} (i : Name (suc n)) (κ : Clock) (j : Fin n)
  → Δ j ≡ removeClock i (insertClockCtx i κ Δ) j
remove-insert' zero κ j = refl
remove-insert' {zero} {Δ} (suc ()) κ
remove-insert' {suc n} {Δ} (suc i) κ zero = refl
remove-insert' {suc n} {Δ} (suc i) κ (suc j) = remove-insert' i κ j

remove-insert : {n : ℕ} {Δ : ClockCtx n} (i : Name (suc n)) (κ : Clock)
  → Δ ≡ removeClock i (insertClockCtx i κ Δ)
remove-insert i κ = funext (remove-insert' i κ)



-- Test

open import Data.Vec

CCtx : ℕ → Set
CCtx = Vec Clock

CCtx≤ : {n : ℕ} → CCtx n → Vec Set n
CCtx≤ Δ = Data.Vec.map Size≤ Δ





--insertClockCtx-refl' : {n : ℕ} (i : Fin (suc n))
--  → (κ : Clock) (Δ : ClockCtx n)
--  → (j : Fin (suc n))
--  → insertClockCtx-lem' i κ κ Δ (coeClockCtx Δ) j ≡ {!!}
--insertClockCtx-refl' = {!!}

{-

insertClockCtx≤ : {n : ℕ} (i : Fin (suc n))
  → (κ : Clock) (α : Size≤ κ)
  → (Δ : ClockCtx n) → ClockCtx≤ (insertClockCtx i κ Δ)
insertClockCtx≤ zero κ α Δ zero = α
insertClockCtx≤ zero κ α Δ (suc j) = coeSize (Δ j)
insertClockCtx≤ {zero} (suc ()) κ α Δ j
insertClockCtx≤ {suc n} (suc i) κ α Δ zero =
  coeSize (Δ zero)
insertClockCtx≤ {suc n} (suc i) κ α Δ (suc j) =
  insertClockCtx≤ i κ α (Δ ∘ suc) j

insertClockCtx≤2 : {n : ℕ} (i : Fin (suc n))
  → (κ : Clock) (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
  → ClockCtx≤ (insertClockCtx i κ Δ)
insertClockCtx≤2 zero κ Δ Δ' zero = κ
insertClockCtx≤2 zero κ Δ Δ' (suc j) = Δ' j
insertClockCtx≤2 {zero} (suc ()) κ Δ Δ' j
insertClockCtx≤2 {suc n} (suc i) κ Δ Δ' zero = Δ' zero
insertClockCtx≤2 {suc n} (suc i) κ Δ Δ' (suc j) =
  insertClockCtx≤2 i κ (Δ ∘ suc) (λ k → Δ' (suc k)) j

insertClockCtx-lem' : {n : ℕ} (i : Fin (suc n))
  → (κ : Clock) (α : Size≤ κ) (Δ : ClockCtx n)
  → (j : Fin (suc n))
  → insertClockCtx i α Δ j ≡ insertClockCtx≤ i κ α Δ j
insertClockCtx-lem' zero κ α Δ zero = refl
insertClockCtx-lem' zero κ α Δ (suc j) = refl
insertClockCtx-lem' {zero} (suc ()) κ α Δ j
insertClockCtx-lem' {suc n} (suc i) κ α Δ zero = refl
insertClockCtx-lem' {suc n} (suc i) κ α Δ (suc j) =
  insertClockCtx-lem' i κ α (Δ ∘ suc) j

insertClockCtx-lem : {n : ℕ} (i : Fin (suc n))
  → (κ : Clock) (α : Size≤ κ) (Δ : ClockCtx n)
  → insertClockCtx i α Δ ≡ insertClockCtx≤ i κ α Δ
insertClockCtx-lem i κ α Δ =
  funext (insertClockCtx-lem' i κ α Δ)
-}




{-
_[_↦_↦_]' : {n : ℕ} (Δ : ClockCtx n) (i : Fin n)
  → (κ₁ : Size≤ (Δ i)) (κ₂ : Size≤ κ₁) (j : Fin n)
  → transSize≤ (((Δ [ i ↦ κ₁ ]≤) [ i ↦ {!!} ]≤) j)
    ≡
    (Δ [ i ↦ transSize≤ {Δ i}{κ₁} κ₂ ]≤) j
(Δ [ i ↦ κ₁ ↦ κ₂ ]') j = {!!}

_[_↦_↦_] : {n : ℕ} (Δ : ClockCtx n) (i : Fin n)
  → (κ₁ κ₂ : Size≤ (Δ i))
  → (Δ [ i ↦ κ₁ ]≤) [ i ↦ κ₂ ] ≡ Δ [ i ↦ κ₂ ]≤
_[_↦_↦_] = {!!}
-}



{-
(Δ [ i ↦ κ₁ ↦ κ₂ ]') j with i ≟ j | inspect (λ z → i ≟ z) j
(Δ [ i ↦ κ₁ ↦ κ₂ ]') .i | yes refl | _ = refl
(Δ [ i ↦ κ₁ ↦ κ₂ ]') j | no ¬p | Reveal_·_is_.[ eq ]
  rewrite eq = refl
-}

{-
-}
-- lhs : ClockCtx≤ (Δ [ i ↦ κ₁ ]≤)
-- rhs : ClockCtx≤ Δ


{-
_[_↦_↦_] : {n : ℕ} (Δ : ClockCtx n) (i : Fin n)
  → (κ₁ κ₂ : Size≤ (Δ i))
  → (Δ [ i ↦ κ₁ ]≤) [ i ↦ κ₂ ]≤ ≡ Δ [ i ↦ κ₂ ]≤
Δ [ i ↦ κ₁ ↦ κ₂ ] = funext (λ j → {!(Δ [ i ↦ κ₁ ↦ κ₂ ]') j!}) --()
-}

{-
_[_↦_] : {n : ℕ} → ClockCtx n → Fin n → Clock → ClockCtx n
(Δ [ i ↦ κ ]) j =
  case (i ≟ j) of (λ { (yes p) → κ ; (no ¬p) → Δ j })
-}
