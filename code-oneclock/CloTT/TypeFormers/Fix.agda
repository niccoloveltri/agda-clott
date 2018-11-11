module CloTT.TypeFormers.Fix where

open import Data.Product
open import Prelude
open import Presheaves.Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.LaterType
open import CloTT.TypeFormers.FunctionType


{-# TERMINATING #-}
dfix-tm : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A)) → Tm tot Γ (▻ A)
proj₁ (proj₁ (dfix-tm Γ A (f , p)) i x) [ j ] = proj₁ (f i x) j (proj₁ (dfix-tm Γ A (f , p)) j (PSh.Mor Γ i j x))
proj₂ (proj₁ (dfix-tm Γ A (f , p)) i x) j k =
  begin
    PSh.Mor A j k (proj₁ (f i x) j (proj₁ (dfix-tm Γ A (f , p)) j (PSh.Mor Γ i j x)))
  ≡⟨ proj₂ (f i x) j k (proj₁ (dfix-tm Γ A (f , p)) j (PSh.Mor Γ i j x)) ⟩ 
    proj₁ (f i x) k (PSh.Mor (▻ A) j k (proj₁ (dfix-tm Γ A (f , p)) j (PSh.Mor Γ i j x)))
  ≡⟨ cong (proj₁ (f i x) k) (proj₂ (dfix-tm Γ A (f , p)) j k (PSh.Mor Γ i j x)) ⟩ 
    proj₁ (f i x) k (proj₁ (dfix-tm Γ A (f , p)) k (PSh.Mor Γ j k (PSh.Mor Γ i j x)))
  ≡⟨ cong (proj₁ (f i x) k) (cong (proj₁ (dfix-tm Γ A (f , p)) k) (sym (PSh.MorComp Γ))) ⟩ 
    proj₁ (f i x) k (proj₁ (dfix-tm Γ A (f , p)) k (PSh.Mor Γ i k x))
  ∎
proj₂ (dfix-tm Γ A (f , p)) i j x =
  Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
         (funext (λ { [ k ] → cong₂ (λ a b → proj₁ a k (proj₁ (dfix-tm Γ A (f , p)) k b)) (p i j x) (PSh.MorComp Γ) }))


fix-tm : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A)) → Tm tot Γ A
fix-tm Γ A f = app {tot} {Γ} {▻ A} {A} f (dfix-tm Γ A f)

dfix-eq : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A))
  → def-eq {tot} Γ (▻ A) (dfix-tm Γ A f) (pure Γ A (fix-tm Γ A f))
dfix-eq Γ A (f , p) i x =
  Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
         (funext (λ { [ j ] → cong (λ a → proj₁ a j (proj₁ (dfix-tm Γ A (f , p)) j (PSh.Mor Γ i j x))) (p i j x) }))

fix-eq : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A))
  → def-eq {tot} Γ A (fix-tm Γ A f) (app {tot} {Γ} {▻ A} {A} f (pure Γ A (fix-tm Γ A f)))
fix-eq Γ A f i x = cong (proj₁ (proj₁ f i x) i) (dfix-eq Γ A f i x)





{-
dfix : (A : Size → Set) (i : Size) (f : (j : Size≤ i) → Later A j → A j)
  → Later A i
dfix A i f [ j ] = f j (dfix A j f)
-}








{-
fix-tm' : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A))
  → Tm tot Γ A
dfix-tm' : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A))
  → Tm tot Γ (▻ A)
fix-tm' Γ A f = {!!}
dfix-tm' Γ A f = {!!}
-}


{-
mutual
  dfix-tm₁₁ : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A))
    → (i : Size) (x : PSh.Obj Γ i) → Later (PSh.Obj A) i
  dfix-tm₁₁ Γ A (f , p) i x [ j ] = proj₁ (f i x) j (dfix-tm₁ Γ A (f , p) j (PSh.Mor Γ i j x))

  dfix-tm₁₂' : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A))
    → (i : Size) (x : PSh.Obj Γ i)
    → (j : Size< i) (k : Size≤ j)
    → (y : {!!})
    → PSh.Mor A j k (proj₁ (proj₁ f i x) j {!!}) ≡ {!proj₁ (proj₁ f i x) j!}
  dfix-tm₁₂' = {!!}

  dfix-tm₁₂ : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A))
    → (i : Size) (x : PSh.Obj Γ i)
    → (j : Size< i) (k : Size≤ j)
    → PSh.Mor A j k (dfix-tm₁₁ Γ A f i x [ j ]) ≡ dfix-tm₁₁ Γ A f i x [ k ]
  dfix-tm₁₂ Γ A (f , p) i x j k = 
    begin
      PSh.Mor A j k (proj₁ (f i x) j (dfix-tm₁ Γ A (f , p) j (PSh.Mor Γ i j x)))
    ≡⟨ {!!} ⟩ --proj₂ (f i x) j k (proj₁ (dfix-tm Γ A (f , p)) j (PSh.Mor Γ i j x)) ⟩ 
      --proj₁ (f i x) k (PSh.Mor (▻ A) j k (proj₁ (dfix-tm Γ A (f , p)) j (PSh.Mor Γ i j x)))
    --≡⟨ cong (proj₁ (f i x) k) (proj₂ (dfix-tm Γ A (f , p)) j k (PSh.Mor Γ i j x)) ⟩ 
      --proj₁ (f i x) k (proj₁ (dfix-tm Γ A (f , p)) k (PSh.Mor Γ j k (PSh.Mor Γ i j x)))
    --≡⟨ cong (proj₁ (f i x) k) (cong (proj₁ (dfix-tm Γ A (f , p)) k) (sym (PSh.MorComp Γ))) ⟩ 
      proj₁ (f i x) k (dfix-tm₁ Γ A (f , p) k (PSh.Mor Γ i k x))
    ∎

  dfix-tm₁ : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A))
    → (i : Size) (x : PSh.Obj Γ i) → ▻Obj A i
  dfix-tm₁ Γ A (f , p) i x = dfix-tm₁₁ Γ A (f , p) i x , {!!}

  dfix-tm₂ : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A))
    → (i : Size) (j : Size≤ i) (x : PSh.Obj Γ i)
    → PSh.Mor (▻ A) i j (dfix-tm₁ Γ A f i x) ≡ dfix-tm₁ Γ A f j (PSh.Mor Γ i j x)
  dfix-tm₂ Γ A (f , p) i j x = 
    Σ≡-uip (funext (λ { _ → funext (λ _ → uip) }))
           (funext (λ { [ k ] → cong₂ (λ a b → proj₁ a k (dfix-tm₁ Γ A (f , p) k b)) (p i j x) (PSh.MorComp Γ) }))
-}



{-
module _ where

  open import CloTT.TypeFormers.WeakenClock
  open import Data.Unit

  Γ : Ctx tot
  Γ = WC ⊤
  A = Γ
  f : Tm tot Γ (▻ A ⇒ A)
  f = (λ i _ → (λ j x → tt) , (λ j k x → refl)) , λ i j x → refl

  x : Tm tot Γ (▻ A)
  x = dfix-tm Γ A f

  x' : (i : Size) → Later (λ _ → ⊤) i
  x' i = {!proj₁ (proj₁ x i tt)!}
-}

{-
fix : (A : Size → Set) (f : (i : Size) → Later A i → A i)
  → (i : Size) → A i
fix A f i = f i (dfix A f i)
-}
{-
dfix : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A)) → Tm tot Γ (▻ A)
proj₁ (proj₁ (dfix Γ A (f , p)) i x) [ j ] = proj₁ (f i x) j (proj₁ (dfix Γ A (f , p)) j (PSh.Mor Γ i j x))
proj₂ (proj₁ (dfix Γ A f) i x) j k = {!!}
proj₂ (dfix Γ A f) = {!!}
-}
{-
mutual 
  dfix : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A)) → Tm tot Γ (▻ A)
  proj₁ (proj₁ (dfix Γ A f) i x) [ j ] = proj₁ (fix Γ A f) j (PSh.Mor Γ i j x)
  proj₂ (proj₁ (dfix Γ A f) i x) j k =
    begin
      PSh.Mor A j k (proj₁ (proj₁ (dfix Γ A f) i x) [ j ])
    ≡⟨ {!proj₂ (fix Γ A f) j k (PSh.Mor Γ i j x)!} ⟩
      proj₁ (proj₁ (dfix Γ A f) i x) [ k ]
    ∎
  proj₂ (dfix Γ A f) = {!!}
{-
      ≡
      proj₁ (f k (PSh.Mor Γ i k x)) k
      (proj₁ (dfix Γ A (f , p)) k (PSh.Mor Γ i k x))
-}

  fix : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A)) → Tm tot Γ A
  proj₁ (fix Γ A (f , p)) i x = proj₁ (f i x) i (proj₁ (dfix Γ A (f , p)) i x) 
  proj₂ (fix Γ A f) = {!!}
-}

--fix : (A : Size → Set)
--  → (f : (i : Size) (j : Size≤ i) → Later A j → A j)
--  → (i : Size) → A i
--dfix : (A : Size → Set)
--  → (f : (i : Size) (j : Size≤ i) → Later A j → A j)
--  → (i : Size) → Later A i
--fix A f i = f i i (dfix A f i)
--force (dfix A f i) j = fix A f j

{-
fix : (A : Size → Set) (i : Size)
  → (f : (j : Size≤ i) → Later A j → A j)
  → A i
dfix : (A : Size → Set) (i : Size)
  → (f : (j : Size≤ i) → Later A j → A j)
  → Later A i
fix A i f = f i (dfix A i f)
force (dfix A i f) j = fix A j f
-}

{-
fix : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A))
  → (i : Size) (x : PSh.Obj Γ i) → PSh.Obj A i
dfix : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A))
  → (i : Size) (x : PSh.Obj Γ i) → ▻Obj A i
fix Γ A (f , p) i x = proj₁ (f i x) i (dfix Γ A (f , p) i x)
force (proj₁ (dfix Γ A (f , p) i x)) j = fix Γ A (f , p) j (PSh.Mor Γ i j x)
proj₂ (dfix Γ A (f , p) i x) j k = {!p i j x!}
  where
    q : {!!}
    q =   
      begin
        PSh.Mor A j k
          (proj₁ (f j (PSh.Mor Γ i j x)) j
          (dfix Γ A (f , p) j (PSh.Mor Γ i j x)))
      ≡⟨ {!proj₂ (f k (PSh.Mor Γ i k x)) k k (dfix Γ A (f , p) k (PSh.Mor Γ i k x))!} ⟩
        proj₁ (f k (PSh.Mor Γ i k x)) k (dfix Γ A (f , p) k (PSh.Mor Γ i k x))
      ∎
-}   

{-
fix : (A : PSh) (i : Size)
  → (f : (j : Size≤ i) (x : Later (PSh.Obj A) j) (p : (k : Size< j) (l : Size≤ k) → (PSh.Mor A) k l (force x k) ≡ force x l ) → PSh.Obj A j)
  → PSh.Obj A i
dfix : (A : PSh) (i : Size)
  → (f : (j : Size≤ i) (x : Later (PSh.Obj A) j) (p : (k : Size< j) (l : Size≤ k) → (PSh.Mor A) k l (force x k) ≡ force x l ) → PSh.Obj A j)
  → Later (PSh.Obj A) i
pfix : (A : PSh) (i : Size)
  → (f : (j : Size≤ i) (x : Later (PSh.Obj A) j) (p : (k : Size< j) (l : Size≤ k) → (PSh.Mor A) k l (force x k) ≡ force x l ) → PSh.Obj A j)
  → (j : Size< i) (k : Size≤ j) → PSh.Mor A j k (force (dfix A i f) j) ≡ force (dfix A i f) k
fix A i f = f i (dfix A i f) (pfix A i f)
force (dfix A i f) j = fix A j f
pfix A i f j k = {!!}


fix-tm : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A)) → Tm tot Γ A
proj₁ (fix-tm Γ A (f , p)) i x = {!!}
--fix (PSh.Obj A) i g
--  where
--    g : (j : Size≤ i) → Later (PSh.Obj A) j → PSh.Obj A j
--    g j y = proj₁ (f i x) j (y , {!!})
proj₂ (fix-tm Γ A f) = {!!}
-}

{-
fix : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A))
  → (i : Size) (x : PSh.Obj Γ i) → PSh.Obj A i
dfix : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A))
  → (i : Size) (x : PSh.Obj Γ i) → ▻Obj A i
fix Γ A (f , p) i x = proj₁ (f i x) i (dfix Γ A (f , p) i x)
force (proj₁ (dfix Γ A (f , p) i x)) j = fix Γ A (f , p) j (PSh.Mor Γ i j x)
proj₂ (dfix Γ A (f , p) i x) j k = {!proj₂ (f k (PSh.Mor Γ i k x)) k k (dfix Γ A (f , p) k (PSh.Mor Γ i k x))!}

fix-tm : (Γ : Ctx tot) (A : Ty tot) (f : Tm tot Γ (▻ A ⇒ A)) → Tm tot Γ A
proj₁ (fix-tm Γ A (f , _)) i = {!!}
proj₂ (fix-tm Γ A f) = {!!}
-}


{-
fix₁ : {n : ℕ} (Γ : Ctx (suc n)) (A : Ty (suc n)) (i : Name (suc n))
          → (f : Tm Γ (Later A i ⇒ A))
          → (Δ : ClockCtx n) → (j : Clock)
          → Ctx.Obj Γ (insertClockCtx i j Δ) → Ctx.Obj A (insertClockCtx i j Δ)
dfix₁ : {n : ℕ} (Γ : Ctx (suc n)) (A : Ty (suc n)) (i : Name (suc n))
          → (f : Tm Γ (Later A i ⇒ A))
          → (Δ : ClockCtx n) → (j : Clock)
          → Ctx.Obj Γ (insertClockCtx i j Δ) → LaterObj A i (insertClockCtx i j Δ)
fix₁ Γ A i (f , p) Δ j x = proj₁ (f (insertClockCtx i j Δ) x) _ (dfix₁ Γ A i (f , p) Δ j x)
force (proj₁ (dfix₁ Γ A i (f , p) Δ j x)) α = Ctx.Mor A (insertClockCtx i α Δ) _ (fix₁ Γ A i (f , p) Δ α (Ctx.Mor Γ (insertClockCtx i j Δ) _ x))
proj₂ (dfix₁ Γ A i (f , p) Δ j x) = {!!}

{-
fix₁ : {n : ℕ} (Γ : Ctx n) (A : Ty n) (i : Name n)
          → (f : Tm Γ (Later A i ⇒ A))
          → (Δ : ClockCtx n) → Ctx.Obj Γ Δ → Ctx.Obj A Δ
dfix₁ : {n : ℕ} (Γ : Ctx n) (A : Ty n) (i : Name n)
          → (f : Tm Γ (Later A i ⇒ A))
          → (Δ : ClockCtx n) → Ctx.Obj Γ Δ → LaterObj A i Δ
fix₁ Γ A i (f , p) Δ x = proj₁ (f Δ x) _ (dfix₁ Γ A i (f , p) Δ x) 
force (proj₁ (dfix₁ Γ A i (f , p) Δ x)) α = fix₁ Γ A i (f , p) {!!} (Ctx.Mor Γ Δ _ x)
proj₂ (dfix₁ Γ A i (f , p) Δ x) = {!!}
-}

fix : {n : ℕ} (Γ : Ctx n) (A : Ty n) (i : Name n)
          → (e : Tm Γ (Later A i ⇒ A)) → Tm Γ A
proj₁ (fix Γ A i e) = {!!}         
proj₂ (fix Γ A i e) = {!!}         

-}
