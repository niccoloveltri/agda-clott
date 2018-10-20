{-
The later modality as a presheaf.
We start by presenting a modality ▻.
Given a type A depending on n clocks and a name i, it returns a type ▻ A depending on n clocks.
The type ▻ A represents A, but lazily evaluated.
Lazy computations can be forced by providing a resources and these resources are ticks.
It is defined coinductively and force is how to make observations.
We define bisimilarity of lazy computations and we postulate that bisimilar computations are equal.
Lastly, we show that we can turn this into a type.

The structure of this file is as follows:
1. The ▻ modality
2. Bisimilarity implies equality
3. Object part
4. Morphism part
5. Preservation of identity
6. Preservation of composition
-}
module CloTT.TypeFormers.Later where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure

module _ {n : ℕ} (A : Ty n) (i : Name n) where

  private module A = Ty A

  -- 1. The ▻ modality
  record ▻ (Δ : ClockCtx n) : Set where
    coinductive
    field
      force : (α : TickCtx Δ i) → A.Obj (Δ [ i ↦ α ])
  open ▻

  -- 2. Bisimilarity implies equality
  _∼_ : {Δ : ClockCtx n} (x y : ▻ Δ) → Set
  x ∼ y = force x ≡ force y

  postulate
    bisim : {Δ : ClockCtx n} {x y : ▻ Δ} → x ∼ y → x ≡ y

  -- 3. Object part
  LaterObj : (Δ : ClockCtx n) → Set
  LaterObj Δ =
    Σ (▻ Δ)
      (λ x → (α : Tick (Δ i)) (α' : Size≤ α)
        → A.Mor (Δ [ i ↦ α ]) _ (force x α)
          ≡
          force x (transSize<≤ {Δ i} {α} α')) 

  -- 4. Morphism part
  LaterMor' : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
    → ▻ Δ → ▻ Δ'
  force (LaterMor' Δ Δ' x) α =
    A.Mor (Δ [ i ↦ α ]) _ (force x (transSize≤< {Δ i}{Δ' i} α))

  LaterMor : (Δ : ClockCtx n) (Δ' : ClockCtx≤ Δ)
    → LaterObj Δ → LaterObj Δ'
  proj₁ (LaterMor Δ Δ' (x , p)) = LaterMor' Δ Δ' x
  proj₂ (LaterMor Δ Δ' (x , p)) α α' =
    begin
      A.Mor (Δ' [ i ↦ α ]) _
        (A.Mor (Δ [ i ↦ α ]) _ (force x (transSize≤< {Δ i}{Δ' i} α)))
    ≡⟨ sym A.MorComp ⟩ 
      A.Mor (Δ [ i ↦ α ]) _ (force x (transSize≤< {Δ i}{Δ' i} α))
    ≡⟨ A.MorComp ⟩
      A.Mor (Δ [ i ↦ α' ]) _ (A.Mor (Δ [ i ↦ α ] ) _ (force x _))
    ≡⟨ cong (A.Mor (Δ [ i ↦ α' ]) _) (p _ _) ⟩ 
      A.Mor (Δ [ i ↦ α' ]) _
        (force x (transSize≤< {Δ i} α'))
    ∎
  
  -- 5. Preservation of identity
  forceLaterMorId : {Δ : ClockCtx n} {x : ▻ Δ}
             → force (LaterMor' Δ (coeClockCtx Δ) x) ≡ force x
  forceLaterMorId = funext (λ {j → A.MorId})

  LaterMorId : {Δ : ClockCtx n} {x : LaterObj Δ}
             → LaterMor Δ (coeClockCtx Δ) x ≡ x
  LaterMorId {Δ} {x₁ , x₂} =
     Σ≡-uip (funext (λ {_ → funext (λ _ → uip)}))
            (bisim (forceLaterMorId {_} {x₁}))

  -- 6. Preservation of composition
  forceLaterMorComp : {Δ : ClockCtx n} {Δ' : ClockCtx≤ Δ} {Δ'' : ClockCtx≤ Δ'} {x : ▻ Δ}
               → force (LaterMor' Δ _ x) ≡ force (LaterMor' Δ' Δ'' (LaterMor' Δ Δ' x))
  forceLaterMorComp = funext (λ {j → A.MorComp})

  LaterMorComp : {Δ : ClockCtx n} {Δ' : ClockCtx≤ Δ} {Δ'' : ClockCtx≤ Δ'} {x : LaterObj Δ}
               → LaterMor Δ _ x ≡ LaterMor Δ' Δ'' (LaterMor Δ Δ' x)
  LaterMorComp {_} {_} {_} {x₁ , x₂} =
    Σ≡-uip (funext (λ {_ → funext (λ _ → uip)}))
           (bisim (forceLaterMorComp {_} {_} {_} {x₁}))

  Later : Ty n
  Later = record
    { Obj = LaterObj
    ; Mor = LaterMor
    ; MorId = LaterMorId
    ; MorComp = LaterMorComp
    }


{-

  LaterObj : (Δ : ClockCtx n) → Set
  LaterObj Δ =
    Σ (▻ Δ)
      (λ x → (α : Tick (Δ i)) (α' : Size≤ ((Δ [ i ↦ α ]) i))
        → A.Mor (Δ [ i ↦ α ]) ((Δ [ i ↦ α ]) [ i ↦ α' ]≤) (force x α)
          ≡
          subst A.Obj {!!} (force x {!!}))
{-
      (λ x → (α : Tick (Δ i)) (α' : Size≤ α)
        → A.Mor (Δ [ i ↦ α ]) ((Δ [ i ↦ α ])
                [ i ↦ subst Size≤ (sym (id[↦] {Δ = Δ}{i}{α})) α' ]≤) (force x α)
          ≡
          subst A.Obj {!!} (force x (transSize< {Δ i}{α} α' ))) 
-}


  Later : Ty n
  Later = record
    { Obj = {!!} --LaterObj
    ; Mor = {!!}
    ; MorId = {!!}
    ; MorComp = {!!}
    }
-}
