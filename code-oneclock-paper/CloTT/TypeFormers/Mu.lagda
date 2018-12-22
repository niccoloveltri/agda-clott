\AgdaHide{
\begin{code}
module CloTT.TypeFormers.Mu where

open import Data.Sum renaming (map to map⊎)
open import Data.Product renaming (map to map×)
open import Prelude
open import Prelude.Syntax
open import Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.SumType
open import CloTT.TypeFormers.ProductType
open import CloTT.TypeFormers.FunctionType
open import CloTT.TypeFormers.WeakenClock

open PSh
\end{code}
}

\begin{code}
data SemPoly : tag → Set₁ where
    ∁s : Set → SemPoly set
    ∁ps : PSh → SemPoly tot
    I : {Δ : tag} → SemPoly Δ
    _⊞_ : {Δ : tag} → SemPoly Δ → SemPoly Δ → SemPoly Δ
    _⊠_ : {Δ : tag} → SemPoly Δ → SemPoly Δ → SemPoly Δ
    ► : SemPoly tot → SemPoly tot
\end{code}

\begin{code}
eval : {Δ : tag} → SemPoly Δ → Ty Δ → Ty Δ
eval (∁s A) X = A
eval (∁ps A) X = A
eval I X = X
eval (P ⊞ Q) X = eval P X ⊕ eval Q X
eval (P ⊠ Q) X = eval P X ⊗ eval Q X
eval (► P) X = ▻(eval P X)
\end{code}

\begin{code}
data μset (P : SemPoly set) : SemPoly set → Set where
  ∁s : {X : Set} → X → μset P (∁s X)
  I : μset P P → μset P I
  _⊠_ : {Q R : SemPoly set} → μset P Q → μset P R → μset P (Q ⊠ R)
  ⊞₁ : {Q R : SemPoly set} → μset P Q → μset P (Q ⊞ R)
  ⊞₂ : {Q R : SemPoly set} → μset P R → μset P (Q ⊞ R)
\end{code}

\begin{code}
mutual
  data μObj' (P : SemPoly tot) : SemPoly tot → Size → Set where
    ∁ps : {X : PSh} {i : Size} → Obj X i → μObj' P (∁ps X) i
    I : ∀{i} → μObj' P P i → μObj' P I i
    _⊠_ : ∀{Q}{R}{i} → μObj' P Q i → μObj' P R i → μObj' P (Q ⊠ R) i
    ⊞₁ : ∀{Q}{R}{i} → μObj' P Q i → μObj' P (Q ⊞ R) i
    ⊞₂ : ∀{Q}{R}{i} → μObj' P R i → μObj' P (Q ⊞ R) i
    ► : ∀{Q}{i} (x : Later (μObj' P Q) i) → LaterLim (μObj' P Q) (μMor' P Q) i x → μObj' P (► Q) i

  μMor' : (P Q : SemPoly tot) (i : Size) (j : Size< (↑ i)) → μObj' P Q i → μObj' P Q j
  μMor' P (∁ps X) i j (∁ps x) = ∁ps (Mor X i j x)
  μMor' P I i j (I x) = I (μMor' P P i j x)
  μMor' P (Q ⊠ R) i j (x ⊠ y) = μMor' P Q i j x ⊠ μMor' P R i j y
  μMor' P (Q ⊞ R) i j (⊞₁ x) = ⊞₁ (μMor' P Q i j x)
  μMor' P (Q ⊞ R) i j (⊞₂ x) = ⊞₂ (μMor' P R i j x)
  μMor' P (► Q) i j (► x p) = ► x p'
    where
      p' : LaterLim (μObj' P Q) (μMor' P Q) j x
      p' [ k ] [ l ] = p [ k ] [ l ]
\end{code}

\begin{code}
μMor'Id : (P Q : SemPoly tot) {i : Size} {x : μObj' P Q i} → μMor' P Q i i x ≡ x
μMor'Id P (∁ps X) {i} {∁ps x} = cong ∁ps (MorId X)
μMor'Id P I {i}{I x} = cong I (μMor'Id P P)
μMor'Id P (Q ⊠ R) {i}{x ⊠ y} = cong₂ _⊠_ (μMor'Id P Q) (μMor'Id P R)
μMor'Id P (Q ⊞ R) {i}{⊞₁ x} = cong ⊞₁ (μMor'Id P Q)
μMor'Id P (Q ⊞ R) {i}{⊞₂ x} = cong ⊞₂ (μMor'Id P R)
μMor'Id P (► Q) {i}{► x p} = cong₂-dep ► refl (funext (λ { [ j ] → funext (λ { [ k ] → refl }) }))
\end{code}

\begin{code}
μMor'Comp : (P Q : SemPoly tot) {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)} {x : μObj' P Q i}
  → μMor' P Q i k x ≡ μMor' P Q j k (μMor' P Q i j x)
μMor'Comp P (∁ps X) {x = ∁ps x} = cong ∁ps (MorComp X)
μMor'Comp P I {x = I x} = cong I (μMor'Comp P P)
μMor'Comp P (Q ⊠ R) {x = x ⊠ y} = cong₂ _⊠_ (μMor'Comp P Q) (μMor'Comp P R)
μMor'Comp P (Q ⊞ R) {x = ⊞₁ x} = cong ⊞₁ (μMor'Comp P Q)
μMor'Comp P (Q ⊞ R) {x = ⊞₂ x} = cong ⊞₂ (μMor'Comp P R)
μMor'Comp P (► Q) {x = ► x p} = cong₂-dep ► refl (funext (λ { [ j ] → funext (λ { [ k ] → refl }) }))
\end{code}

\begin{code}
μpsh : SemPoly tot → SemPoly tot → Ty tot
μpsh P Q = record
  { Obj = μObj' P Q
  ; Mor = μMor' P Q
  ; MorId = μMor'Id P Q
  ; MorComp = μMor'Comp P Q
  }
\end{code}

\begin{code}
mu : {Δ : tag} → (P : SemPoly Δ) → Ty Δ
mu {set} P = μset P P
mu {tot} P = μpsh P P
\end{code}

rec₁₁' : ∀ P Q A i
  → (f : (j : Size< (↑ i)) → Obj (eval P A) j → Obj A j)
  → (p : (j : Size< (↑ i)) (k : Size< (↑ j)) (x : Obj (eval P A) j)
       → Mor A j k (f j x) ≡ f k (Mor (eval P A) j k x))
  → (j : Size< (↑ i)) → μObj' P Q j → Obj (eval Q A) j
rec₁₂' : ∀ P Q A i
  → (f : (j : Size< (↑ i)) → Obj (eval P A) j → Obj A j)
  → (p : (j : Size< (↑ i))(k : Size< (↑ j))(x : Obj (eval P A) j)
       → Mor A j k (f j x) ≡ f k (Mor (eval P A) j k x))
  → (j : Size< (↑ i)) (k : Size< (↑ j)) (x : μObj' P Q j)
  → Mor (eval Q A) j k (rec₁₁' P Q A i f p j x) ≡ rec₁₁' P Q A i f p k (μMor' P Q j k x)
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
  → (f : Tm Γ (eval P A ⇒ A))
  → (i : Size) (j : Size< (↑ i)) (γ : Obj Γ i)
  → (k : Size< (↑ j)) (x : μObj' P Q k)
  → rec₁₁' P Q A i (proj₁ (proj₁ f i γ)) (proj₂ (proj₁ f i γ)) k x ≡
    rec₁₁' P Q A j (proj₁ (proj₁ f j (Mor Γ i j γ))) (proj₂ (proj₁ f j (Mor Γ i j γ))) k x
rec₂' P (∁ X) Γ A f i j γ k (∁ x) = refl
rec₂' P I Γ A (f , p) i j γ k (I x) = cong₂ (λ a b → proj₁ a k b) (p i j γ) (rec₂' P P Γ A (f , p) i j γ k x)
rec₂' P (Q ⊠ R) Γ A f i j γ k (x ⊠ y) = cong₂ _,_ (rec₂' P Q Γ A f i j γ k x) (rec₂' P R Γ A f i j γ k y)
rec₂' P (Q ⊞ R) Γ A f i j γ k (⊞₁ x) = cong inj₁ (rec₂' P Q Γ A f i j γ k x)
rec₂' P (Q ⊞ R) Γ A f i j γ k (⊞₂ x) = cong inj₂ (rec₂' P R Γ A f i j γ k x)
rec₂' P (► Q) Γ A f i j γ k (► x q) =
  Σ≡-uip (funext (λ { [ _ ] → funext (λ { [ _ ] → uip }) })) (funext (λ { [ l ] → rec₂' P Q Γ A f i j γ l (x [ l ]) }))

rec' : ∀ P Q Γ A → Tm Γ (eval P A ⇒ A) → Tm Γ (μ' P Q ⇒ eval Q A)
proj₁ (proj₁ (rec' P Q Γ A (f , p)) i γ) j x = rec₁₁' P Q A i (proj₁ (f i γ)) (proj₂ (f i γ)) j x
proj₂ (proj₁ (rec' P Q Γ A (f , p)) i γ) j k x = rec₁₂' P Q A i (proj₁ (f i γ)) (proj₂ (f i γ)) j k x
proj₂ (rec' P Q Γ A (f , p)) i j γ =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ k → funext (rec₂' P Q Γ A (f , p) i j γ k)))

rec : ∀ P Γ A → Tm Γ (eval P A ⇒ A) → Tm Γ (μ P ⇒ A)
rec P Γ A f =
  lambda Γ (μ P) A
    (app (Γ ,, μ P) (eval P A) A
         wk-f
         (app (Γ ,, μ P) (μ P) (eval P A)
              (rec' P P (Γ ,, μ P) A wk-f)
              (var Γ (μ P))))
  where
    wk-f : Tm (Γ ,, μ P) (eval P A ⇒ A)
    wk-f = weaken Γ (μ P) (eval P A ⇒ A) f

primrec₁₁' : ∀ P Q A i
  → (f : (j : Size< (↑ i)) → Obj (eval P (μ P ⊗ A)) j → Obj A j)
  → (p : (j : Size< (↑ i)) (k : Size< (↑ j)) (x : Obj (eval P (μ P ⊗ A)) j)
       → Mor A j k (f j x) ≡ f k (Mor (eval P (μ P ⊗ A)) j k x))
  → (j : Size< (↑ i)) → μObj' P Q j → Obj (eval Q (μ P ⊗ A)) j
primrec₁₂' : ∀ P Q A i
  → (f : (j : Size< (↑ i)) → Obj (eval P (μ P ⊗ A)) j → Obj A j)
  → (p : (j : Size< (↑ i)) (k : Size< (↑ j)) (x : Obj (eval P (μ P ⊗ A)) j)
       → Mor A j k (f j x) ≡ f k (Mor (eval P (μ P ⊗ A)) j k x))
  → (j : Size< (↑ i)) (k : Size< (↑ j)) (x : μObj' P Q j)
  → Mor (eval Q (μ P ⊗ A)) j k (primrec₁₁' P Q A i f p j x) ≡ primrec₁₁' P Q A i f p k (μMor' P Q j k x)
primrec₁₁' P (∁ X) A i f p j (∁ x) = x
primrec₁₁' P I A i f p j (I x) = x , f j (primrec₁₁' P P A i f p j x)
primrec₁₁' P (Q ⊠ R) A i f p j (x ⊠ y) = (primrec₁₁' P Q A i f p j x) , (primrec₁₁' P R A i f p j y)
primrec₁₁' P (Q ⊞ R) A i f p j (⊞₁ x) = inj₁ (primrec₁₁' P Q A i f p j x)
primrec₁₁' P (Q ⊞ R) A i f p j (⊞₂ x) = inj₂ (primrec₁₁' P R A i f p j x)
proj₁ (primrec₁₁' P (► Q) A i f p j (► x q)) [ k ] = primrec₁₁' P Q A i f p k (x [ k ])
proj₂ (primrec₁₁' P (► Q) A i f p j (► x q)) [ k ] [ l ] = trans (primrec₁₂' P Q A i f p k l (x [ k ])) (cong (primrec₁₁' P Q A i f p l) (q [ k ] [ l ]))
primrec₁₂' P (∁ X) A i f p j k (∁ x) = refl
primrec₁₂' P I A i f p j k (I x) = cong (_,_ _) (trans (p j k (primrec₁₁' P P A i f p j x)) (cong (f k) (primrec₁₂' P P A i f p j k x))) 
primrec₁₂' P (Q ⊠ R) A i f p j k (x ⊠ y) = cong₂ _,_ (primrec₁₂' P Q A i f p j k x) (primrec₁₂' P R A i f p j k y)
primrec₁₂' P (Q ⊞ R) A i f p j k (⊞₁ x) = cong inj₁ (primrec₁₂' P Q A i f p j k x)
primrec₁₂' P (Q ⊞ R) A i f p j k (⊞₂ x) = cong inj₂ (primrec₁₂' P R A i f p j k x)
primrec₁₂' P (► Q) A i f p j k (► x q) = Σ≡-uip (funext (λ { [ _ ] → funext (λ { [ _ ] → uip }) })) (funext (λ { [ l ] → refl }))

primrec₂' : (P Q : Poly) (Γ : Ctx tot) (A : Ty tot)
  → (f : Tm Γ (eval P (μ P ⊗ A) ⇒ A))
  → (i : Size) (j : Size< (↑ i)) (γ : Obj Γ i)
  → (k : Size< (↑ j)) (x : μObj' P Q k)
  → primrec₁₁' P Q A i (proj₁ (proj₁ f i γ)) (proj₂ (proj₁ f i γ)) k x ≡
    primrec₁₁' P Q A j (proj₁ (proj₁ f j (Mor Γ i j γ))) (proj₂ (proj₁ f j (Mor Γ i j γ))) k x
primrec₂' P (∁ X) Γ A f i j γ k (∁ x) = refl
primrec₂' P I Γ A (f , p) i j γ k (I x) = cong (_,_ _) (cong₂ (λ a b → proj₁ a k b) (p i j γ) (primrec₂' P P Γ A (f , p) i j γ k x))
primrec₂' P (Q ⊠ R) Γ A f i j γ k (x ⊠ y) = cong₂ _,_ (primrec₂' P Q Γ A f i j γ k x) (primrec₂' P R Γ A f i j γ k y)
primrec₂' P (Q ⊞ R) Γ A f i j γ k (⊞₁ x) = cong inj₁ (primrec₂' P Q Γ A f i j γ k x)
primrec₂' P (Q ⊞ R) Γ A f i j γ k (⊞₂ x) = cong inj₂ (primrec₂' P R Γ A f i j γ k x)
primrec₂' P (► Q) Γ A f i j γ k (► x q) =
  Σ≡-uip (funext (λ { [ _ ] → funext (λ { [ _ ] → uip }) })) (funext (λ { [ l ] → primrec₂' P Q Γ A f i j γ l (x [ l ]) }))

primrec' : ∀ P Q Γ A → Tm Γ (eval P (μ P ⊗ A) ⇒ A) → Tm Γ (μ' P Q ⇒ eval Q (μ P ⊗ A))
proj₁ (proj₁ (primrec' P Q Γ A (f , p)) i γ) j x = primrec₁₁' P Q A i (proj₁ (f i γ)) (proj₂ (f i γ)) j x
proj₂ (proj₁ (primrec' P Q Γ A (f , p)) i γ) j k x = primrec₁₂' P Q A i (proj₁ (f i γ)) (proj₂ (f i γ)) j k x
proj₂ (primrec' P Q Γ A (f , p)) i j γ =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ k → funext (primrec₂' P Q Γ A (f , p) i j γ k)))

primrec : ∀ P Γ A → Tm Γ (eval P (μ P ⊗ A) ⇒ A) → Tm Γ (μ P ⇒ A)
primrec P Γ A f =
  lambda Γ (μ P) A
    (app (Γ ,, μ P) (eval P (μ P ⊗ A)) A
         wk-f
         (app (Γ ,, μ P) (μ P) (eval P (μ P ⊗ A))
              (primrec' P P (Γ ,, μ P) A wk-f)
              (var Γ (μ P))))
  where
    wk-f : Tm (Γ ,, μ P) (eval P (μ P ⊗ A) ⇒ A)
    wk-f = weaken Γ (μ P) (eval P (μ P ⊗ A) ⇒ A) f

