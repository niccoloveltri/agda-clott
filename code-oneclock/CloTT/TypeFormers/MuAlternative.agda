module CloTT.TypeFormers.MuAlternative where

open import Data.Sum renaming (map to map⊎)
open import Data.Product renaming (map to map×)
open import Prelude
open import Presheaves
open import CloTT.Structure
--open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.ProductType
open import CloTT.TypeFormers.FunctionType
open import CloTT.TypeFormers.WeakenClock

data SizeLt (i : Size) : Set where
  [_] : (j : Size< i) → SizeLt i

size : ∀ {i} → SizeLt i → Size
size [ j ] = j

SizeLe : Size → Set
SizeLe i = SizeLt (↑ i)

elimLt : ∀{ℓ} {A : Size → Set ℓ} {i : Size} (j : SizeLt i)
  → ((j : Size< i) → A j) → A (size j)
elimLt [ j ] f = f j

Later : (Size → Set) → Size → Set
Later A i = (j : SizeLt i) → A (size j)

module _ (A : Size → Set) (m : (i : Size) (j : Size≤ i) → A i → A j)  where

  LaterLim : (i : Size) (x : Later A i) → Set
  LaterLim i x = (j : SizeLt i)
    → elimLt j (λ { j' → (k : SizeLe j')
      → elimLt k (λ k' → m j' k' (x [ j' ]) ≡ x [ k' ]) })

  LaterLimMor : (i : Size) (j : Size≤ i) (x : Later A i)
    → LaterLim i x → LaterLim j x
  LaterLimMor i j x p [ k ] [ l ] = p [ k ] [ l ]

module _ (A : Ty tot) where

  -- 3. Object part
  ▻Obj : (i : Size) → Set
  ▻Obj i = Σ (Later (PSh.Obj A) i) (LaterLim (PSh.Obj A) (PSh.Mor A) i)

  -- 4. Morphism part
  ▻Mor : (i : Size) (j : Size≤ i)
    → ▻Obj i → ▻Obj j
  ▻Mor i j (x , p) = x , LaterLimMor (PSh.Obj A) (PSh.Mor A) i j x p

  -- 5. Preservation of identity
  ▻MorId : {i : Size} {x : ▻Obj i}
             → ▻Mor i i x ≡ x
  ▻MorId = Σ≡-uip (funext (λ { [ j ] → funext (λ { [ k ] → uip }) })) refl

  -- 6. Preservation of composition
  ▻MorComp : {i : Size} {j : Size≤ i} {k : Size≤ j} {x : ▻Obj i}
               → ▻Mor i k x ≡ ▻Mor j k (▻Mor i j x)
  ▻MorComp = Σ≡-uip (funext (λ { [ j ] → funext (λ { [ k ] → uip }) })) refl

  ▻ : Ty tot
  ▻ = record
    { Obj = ▻Obj
    ; Mor = ▻Mor
    ; MorId = ▻MorId
    ; MorComp = ▻MorComp
    }

-- Grammar for polynomials
data Poly : Set₁ where
  ∁ : Set → Poly
  I : Poly
  _⊞_ : Poly → Poly → Poly
  _⊠_ : Poly → Poly → Poly
  ► : Poly → Poly

eval : Poly → PSh → PSh
eval (∁ X) A = WC X
eval I A = A
eval (P ⊞ Q) A = Sum (eval P A) (eval Q A)
eval (P ⊠ Q) A = Prod (eval P A) (eval Q A)
eval (► P) A = ▻ (eval P A)

mutual
  data μObj' (P : Poly) : Poly → Size → Set where
    ∁ : ∀{X}{i} → X → μObj' P (∁ X) i
    I : ∀{i} → μObj' P P i → μObj' P I i
    _⊠_ : ∀{Q}{R}{i} → μObj' P Q i → μObj' P R i → μObj' P (Q ⊠ R) i
    ⊞₁ : ∀{Q}{R}{i} → μObj' P Q i → μObj' P (Q ⊞ R) i
    ⊞₂ : ∀{Q}{R}{i} → μObj' P R i → μObj' P (Q ⊞ R) i
    ► : ∀{Q}{i} (x : Later (μObj' P Q) i) → LaterLim (μObj' P Q) (μMor' P Q) i x → μObj' P (► Q) i

  μMor' : (P Q : Poly) (i : Size) (j : Size≤ i) → μObj' P Q i → μObj' P Q j
  μMor' P (∁ X) i j (∁ x) = ∁ x
  μMor' P I i j (I x) = I (μMor' P P i j x)
  μMor' P (Q ⊠ R) i j (x ⊠ y) = μMor' P Q i j x ⊠ μMor' P R i j y
  μMor' P (Q ⊞ R) i j (⊞₁ x) = ⊞₁ (μMor' P Q i j x)
  μMor' P (Q ⊞ R) i j (⊞₂ x) = ⊞₂ (μMor' P R i j x)
  μMor' P (► Q) i j (► x p) = ► x p'
    where
      p' : LaterLim (μObj' P Q) (μMor' P Q) j x
      p' [ k ] [ l ] = p [ k ] [ l ]

μMor'Id : (P Q : Poly) {i : Size} {x : μObj' P Q i} → μMor' P Q i i x ≡ x
μMor'Id P (∁ X) {i} {∁ x} = refl
μMor'Id P I {i}{I x} = cong I (μMor'Id P P)
μMor'Id P (Q ⊠ R) {i}{x ⊠ y} = cong₂ _⊠_ (μMor'Id P Q) (μMor'Id P R)
μMor'Id P (Q ⊞ R) {i}{⊞₁ x} = cong ⊞₁ (μMor'Id P Q)
μMor'Id P (Q ⊞ R) {i}{⊞₂ x} = cong ⊞₂ (μMor'Id P R)
μMor'Id P (► Q) {i}{► x p} = cong₂-dep ► refl (funext (λ { [ j ] → funext (λ { [ k ] → refl }) }))


μMor'Comp : (P Q : Poly) {i : Size} {j : Size≤ i} {k : Size≤ j} {x : μObj' P Q i}
  → μMor' P Q i k x ≡ μMor' P Q j k (μMor' P Q i j x)
μMor'Comp P (∁ X) {x = ∁ x} = refl
μMor'Comp P I {x = I x} = cong I (μMor'Comp P P)
μMor'Comp P (Q ⊠ R) {x = x ⊠ y} = cong₂ _⊠_ (μMor'Comp P Q) (μMor'Comp P R)
μMor'Comp P (Q ⊞ R) {x = ⊞₁ x} = cong ⊞₁ (μMor'Comp P Q)
μMor'Comp P (Q ⊞ R) {x = ⊞₂ x} = cong ⊞₂ (μMor'Comp P R)
μMor'Comp P (► Q) {x = ► x p} = cong₂-dep ► refl (funext (λ { [ j ] → funext (λ { [ k ] → refl }) }))

μ' : Poly → Poly → Ty tot
μ' P Q = record
  { Obj = μObj' P Q
  ; Mor = μMor' P Q
  ; MorId = μMor'Id P Q
  ; MorComp = μMor'Comp P Q
  }

μ : Poly → Ty tot
μ P = μ' P P

cons₁' : ∀ P Q i → PSh.Obj (eval Q (μ P)) i → μObj' P Q i
cons₂' : ∀ P Q i (j : Size≤ i)(t : PSh.Obj (eval Q (μ P)) i)
  → μMor' P Q i j (cons₁' P Q i t) ≡ cons₁' P Q j (PSh.Mor (eval Q (μ P)) i j t)
cons₁' P (∁ X) i t = ∁ t
cons₁' P I i t = I t
cons₁' P (Q ⊠ R) i (t , u) = (cons₁' P Q i t) ⊠ (cons₁' P R i u)
cons₁' P (Q ⊞ R) i (inj₁ t) = ⊞₁ (cons₁' P Q i t)
cons₁' P (Q ⊞ R) i (inj₂ t) = ⊞₂ (cons₁' P R i t)
cons₁' P (► Q) i (t , p) = ► c₁ c₂
  where
    c₁ : Later (μObj' P Q) i
    c₁ [ j ] = cons₁' P Q j (t [ j ])
    c₂ : LaterLim (μObj' P Q) (μMor' P Q) i c₁
    c₂ [ j ] [ k ] = trans (cons₂' P Q j k (t [ j ])) (cong (cons₁' P Q k) (p [ j ] [ k ]))
cons₂' P (∁ X) i j t = refl
cons₂' P I i j t = refl
cons₂' P (Q ⊠ R) i j (t , u) = cong₂ _⊠_ (cons₂' P Q i j t) (cons₂' P R i j u)
cons₂' P (Q ⊞ R) i j (inj₁ t) = cong ⊞₁ (cons₂' P Q i j t)
cons₂' P (Q ⊞ R) i j (inj₂ t) = cong ⊞₂ (cons₂' P R i j t)
cons₂' P (► Q) i j (t , p) =
  cong₂-dep ► (funext (λ { [ _ ] → refl})) (funext (λ { [ _ ] → funext (λ { [ _ ] → uip }) }))

cons' : ∀ P Q Γ → Tm tot Γ (eval Q (μ P)) → Tm tot Γ (μ' P Q)
proj₁ (cons' P Q Γ (t , p)) i γ  = cons₁' P Q i (t i γ)
proj₂ (cons' P Q Γ (t , p)) i j γ = trans (cons₂' P Q i j (t i γ)) (cong (cons₁' P Q j) (p i j γ))

cons : ∀ P Γ → Tm tot Γ (eval P (μ P)) → Tm tot Γ (μ P)
cons P = cons' P P

rec₁₁' : ∀ P Q A i
  → (f : (j : Size≤ i) → PSh.Obj (eval P A) j → PSh.Obj A j)
  → (p : (j : Size≤ i)(k : Size≤ j)(x : PSh.Obj (eval P A) j)
       → PSh.Mor A j k (f j x) ≡ f k (PSh.Mor (eval P A) j k x))
  → (j : Size≤ i) → μObj' P Q j → PSh.Obj (eval Q A) j
rec₁₂' : ∀ P Q A i
  → (f : (j : Size≤ i) → PSh.Obj (eval P A) j → PSh.Obj A j)
  → (p : (j : Size≤ i)(k : Size≤ j)(x : PSh.Obj (eval P A) j)
       → PSh.Mor A j k (f j x) ≡ f k (PSh.Mor (eval P A) j k x))
  → (j : Size≤ i) (k : Size≤ j) (x : μObj' P Q j)
  → PSh.Mor (eval Q A) j k (rec₁₁' P Q A i f p j x) ≡ rec₁₁' P Q A i f p k (μMor' P Q j k x)
rec₁₁' P (∁ X) A i f p j (∁ x) = x
rec₁₁' P I A i f p j (I x) = f j (rec₁₁' P P A i f p j x)
rec₁₁' P (Q ⊠ R) A i f p j (x ⊠ y) = (rec₁₁' P Q A i f p j x) , (rec₁₁' P R A i f p j y)
rec₁₁' P (Q ⊞ R) A i f p j (⊞₁ x) = inj₁ (rec₁₁' P Q A i f p j x)
rec₁₁' P (Q ⊞ R) A i f p j (⊞₂ x) = inj₂ (rec₁₁' P R A i f p j x)
proj₁ (rec₁₁' P (► Q) A i f p j (► x q)) [ k ] = rec₁₁' P Q A i f p k (x [ k ])
proj₂ (rec₁₁' P (► Q) A i f p j (► x q)) [ k ] [ l ] = trans (rec₁₂' P Q A i f p k l (x [ k ])) (cong (rec₁₁' P Q A i f p l) (q [ k ] [ l ]))
rec₁₂' P (∁ X) A i f p j k (∁ x) = refl
rec₁₂' P I A i f p j k (I x) = trans (p j k (rec₁₁' P P A i f p j x)) (cong (f k) (rec₁₂' P P A i f p j k x))
rec₁₂' P (Q ⊠ R) A i f p j k (x ⊠ y) = cong₂ _,_ (rec₁₂' P Q A i f p j k x) (rec₁₂' P R A i f p j k y)
rec₁₂' P (Q ⊞ R) A i f p j k (⊞₁ x) = cong inj₁ (rec₁₂' P Q A i f p j k x)
rec₁₂' P (Q ⊞ R) A i f p j k (⊞₂ x) = cong inj₂ (rec₁₂' P R A i f p j k x)
rec₁₂' P (► Q) A i f p j k (► x q) = Σ≡-uip (funext (λ { [ _ ] → funext (λ { [ _ ] → uip }) })) (funext (λ { [ l ] → refl }))

rec₂' : (P Q : Poly) (Γ : Ctx tot) (A : Ty tot)
  → (f : Tm tot Γ (eval P A ⇒ A))
  → (i : Size) (j : Size≤ i) (γ : PSh.Obj Γ i)
  → (k : Size≤ j) (x : μObj' P Q k)
  → rec₁₁' P Q A i (proj₁ (proj₁ f i γ)) (proj₂ (proj₁ f i γ)) k x ≡
    rec₁₁' P Q A j (proj₁ (proj₁ f j (PSh.Mor Γ i j γ))) (proj₂ (proj₁ f j (PSh.Mor Γ i j γ))) k x
rec₂' P (∁ X) Γ A f i j γ k (∁ x) = refl
rec₂' P I Γ A (f , p) i j γ k (I x) = cong₂ (λ a b → proj₁ a k b) (p i j γ) (rec₂' P P Γ A (f , p) i j γ k x)
rec₂' P (Q ⊠ R) Γ A f i j γ k (x ⊠ y) = cong₂ _,_ (rec₂' P Q Γ A f i j γ k x) (rec₂' P R Γ A f i j γ k y)
rec₂' P (Q ⊞ R) Γ A f i j γ k (⊞₁ x) = cong inj₁ (rec₂' P Q Γ A f i j γ k x)
rec₂' P (Q ⊞ R) Γ A f i j γ k (⊞₂ x) = cong inj₂ (rec₂' P R Γ A f i j γ k x)
rec₂' P (► Q) Γ A f i j γ k (► x q) =
  Σ≡-uip (funext (λ { [ _ ] → funext (λ { [ _ ] → uip }) })) (funext (λ { [ l ] → rec₂' P Q Γ A f i j γ l (x [ l ]) }))

rec' : ∀ P Q Γ A → Tm tot Γ (eval P A ⇒ A) → Tm tot Γ (μ' P Q ⇒ eval Q A)
proj₁ (proj₁ (rec' P Q Γ A (f , p)) i γ) j x = rec₁₁' P Q A i (proj₁ (f i γ)) (proj₂ (f i γ)) j x
proj₂ (proj₁ (rec' P Q Γ A (f , p)) i γ) j k x = rec₁₂' P Q A i (proj₁ (f i γ)) (proj₂ (f i γ)) j k x
proj₂ (rec' P Q Γ A (f , p)) i j γ =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ k → funext (rec₂' P Q Γ A (f , p) i j γ k)))


rec : ∀ P Γ A → Tm tot Γ (eval P A ⇒ A) → Tm tot Γ (μ P ⇒ A)
rec P Γ A f =
  lambda Γ (μ P) A
    (app {_}{Γ ,, μ P}{eval P A}{A} wk-f
                                    (app {_}{Γ ,, μ P}{μ P}{eval P A} (rec' P P (Γ ,, μ P) A wk-f)
                                                                      (var Γ (μ P))))
  where
    wk-f : Tm tot (Γ ,, μ P) (eval P A ⇒ A)
    wk-f = weaken Γ (μ P) (eval P A ⇒ A) f


