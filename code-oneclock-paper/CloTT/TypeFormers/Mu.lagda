\AgdaHide{
\begin{code}
module CloTT.TypeFormers.Mu where

open import Data.Sum renaming (map to map⊎)
open import Data.Product renaming (map to map×)
open import Prelude
open import Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers.Later
open import CloTT.TypeFormers.ProductType
open import CloTT.TypeFormers.FunctionType
open import CloTT.TypeFormers.WeakenClock
\end{code}
}

\begin{code}
data Poly : Set₁ where
  ∁ : Set → Poly
  I : Poly
  _⊞_ : Poly → Poly → Poly
  _⊠_ : Poly → Poly → Poly
  ► : Poly → Poly
\end{code}

\begin{code}
eval : Poly → PSh → PSh
eval (∁ X) A = WC X
eval I A = A
eval (P ⊞ Q) A = Sum (eval P A) (eval Q A)
eval (P ⊠ Q) A = Prod (eval P A) (eval Q A)
eval (► P) A = ▻ (eval P A)
\end{code}

\begin{code}
mutual
  data μObj' (P : Poly) : Poly → Size → Set where
    ∁ : ∀{X}{i} → X → μObj' P (∁ X) i
    I : ∀{i} → μObj' P P i → μObj' P I i
    _⊠_ : ∀{Q}{R}{i} → μObj' P Q i → μObj' P R i → μObj' P (Q ⊠ R) i
    ⊞₁ : ∀{Q}{R}{i} → μObj' P Q i → μObj' P (Q ⊞ R) i
    ⊞₂ : ∀{Q}{R}{i} → μObj' P R i → μObj' P (Q ⊞ R) i
    ► : ∀{Q}{i} (x : Later (μObj' P Q) i) → LaterLim (μObj' P Q) (μMor' P Q) i x → μObj' P (► Q) i

  μMor' : (P Q : Poly) (i : Size) (j : Size< (↑ i)) → μObj' P Q i → μObj' P Q j
  μMor' P (∁ X) i j (∁ x) = ∁ x
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
μMor'Id : (P Q : Poly) {i : Size} {x : μObj' P Q i} → μMor' P Q i i x ≡ x
μMor'Id P (∁ X) {i} {∁ x} = refl
μMor'Id P I {i}{I x} = cong I (μMor'Id P P)
μMor'Id P (Q ⊠ R) {i}{x ⊠ y} = cong₂ _⊠_ (μMor'Id P Q) (μMor'Id P R)
μMor'Id P (Q ⊞ R) {i}{⊞₁ x} = cong ⊞₁ (μMor'Id P Q)
μMor'Id P (Q ⊞ R) {i}{⊞₂ x} = cong ⊞₂ (μMor'Id P R)
μMor'Id P (► Q) {i}{► x p} = cong₂-dep ► refl (funext (λ { [ j ] → funext (λ { [ k ] → refl }) }))
\end{code}

\begin{code}
μMor'Comp : (P Q : Poly) {i : Size} {j : Size< (↑ i)} {k : Size< (↑ j)} {x : μObj' P Q i}
  → μMor' P Q i k x ≡ μMor' P Q j k (μMor' P Q i j x)
μMor'Comp P (∁ X) {x = ∁ x} = refl
μMor'Comp P I {x = I x} = cong I (μMor'Comp P P)
μMor'Comp P (Q ⊠ R) {x = x ⊠ y} = cong₂ _⊠_ (μMor'Comp P Q) (μMor'Comp P R)
μMor'Comp P (Q ⊞ R) {x = ⊞₁ x} = cong ⊞₁ (μMor'Comp P Q)
μMor'Comp P (Q ⊞ R) {x = ⊞₂ x} = cong ⊞₂ (μMor'Comp P R)
μMor'Comp P (► Q) {x = ► x p} = cong₂-dep ► refl (funext (λ { [ j ] → funext (λ { [ k ] → refl }) }))
\end{code}

\begin{code}
μ' : Poly → Poly → Ty tot
μ' P Q = record
  { Obj = μObj' P Q
  ; Mor = μMor' P Q
  ; MorId = μMor'Id P Q
  ; MorComp = μMor'Comp P Q
  }
\end{code}

\begin{code}
μ : Poly → Ty tot
μ P = μ' P P
\end{code}

\begin{code}
cons₁' : ∀ P Q i → PSh.Obj (eval Q (μ P)) i → μObj' P Q i
cons₂' : ∀ P Q i (j : Size< (↑ i))(t : PSh.Obj (eval Q (μ P)) i)
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
\end{code}

\begin{code}
cons' : ∀ P Q Γ → Tm Γ (eval Q (μ P)) → Tm Γ (μ' P Q)
proj₁ (cons' P Q Γ (t , p)) i γ  = cons₁' P Q i (t i γ)
proj₂ (cons' P Q Γ (t , p)) i j γ = trans (cons₂' P Q i j (t i γ)) (cong (cons₁' P Q j) (p i j γ))
\end{code}

\begin{code}
cons : ∀ P Γ → Tm Γ (eval P (μ P)) → Tm Γ (μ P)
cons P = cons' P P
\end{code}

\begin{code}
rec₁₁' : ∀ P Q A i
  → (f : (j : Size< (↑ i)) → PSh.Obj (eval P A) j → PSh.Obj A j)
  → (p : (j : Size< (↑ i)) (k : Size< (↑ j)) (x : PSh.Obj (eval P A) j)
       → PSh.Mor A j k (f j x) ≡ f k (PSh.Mor (eval P A) j k x))
  → (j : Size< (↑ i)) → μObj' P Q j → PSh.Obj (eval Q A) j
rec₁₂' : ∀ P Q A i
  → (f : (j : Size< (↑ i)) → PSh.Obj (eval P A) j → PSh.Obj A j)
  → (p : (j : Size< (↑ i))(k : Size< (↑ j))(x : PSh.Obj (eval P A) j)
       → PSh.Mor A j k (f j x) ≡ f k (PSh.Mor (eval P A) j k x))
  → (j : Size< (↑ i)) (k : Size< (↑ j)) (x : μObj' P Q j)
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
\end{code}

\begin{code}
rec₂' : (P Q : Poly) (Γ : Ctx tot) (A : Ty tot)
  → (f : Tm Γ (eval P A ⇒ A))
  → (i : Size) (j : Size< (↑ i)) (γ : PSh.Obj Γ i)
  → (k : Size< (↑ j)) (x : μObj' P Q k)
  → rec₁₁' P Q A i (proj₁ (proj₁ f i γ)) (proj₂ (proj₁ f i γ)) k x ≡
    rec₁₁' P Q A j (proj₁ (proj₁ f j (PSh.Mor Γ i j γ))) (proj₂ (proj₁ f j (PSh.Mor Γ i j γ))) k x
rec₂' P (∁ X) Γ A f i j γ k (∁ x) = refl
rec₂' P I Γ A (f , p) i j γ k (I x) = cong₂ (λ a b → proj₁ a k b) (p i j γ) (rec₂' P P Γ A (f , p) i j γ k x)
rec₂' P (Q ⊠ R) Γ A f i j γ k (x ⊠ y) = cong₂ _,_ (rec₂' P Q Γ A f i j γ k x) (rec₂' P R Γ A f i j γ k y)
rec₂' P (Q ⊞ R) Γ A f i j γ k (⊞₁ x) = cong inj₁ (rec₂' P Q Γ A f i j γ k x)
rec₂' P (Q ⊞ R) Γ A f i j γ k (⊞₂ x) = cong inj₂ (rec₂' P R Γ A f i j γ k x)
rec₂' P (► Q) Γ A f i j γ k (► x q) =
  Σ≡-uip (funext (λ { [ _ ] → funext (λ { [ _ ] → uip }) })) (funext (λ { [ l ] → rec₂' P Q Γ A f i j γ l (x [ l ]) }))
\end{code}

\begin{code}
rec' : ∀ P Q Γ A → Tm Γ (eval P A ⇒ A) → Tm Γ (μ' P Q ⇒ eval Q A)
proj₁ (proj₁ (rec' P Q Γ A (f , p)) i γ) j x = rec₁₁' P Q A i (proj₁ (f i γ)) (proj₂ (f i γ)) j x
proj₂ (proj₁ (rec' P Q Γ A (f , p)) i γ) j k x = rec₁₂' P Q A i (proj₁ (f i γ)) (proj₂ (f i γ)) j k x
proj₂ (rec' P Q Γ A (f , p)) i j γ =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ k → funext (rec₂' P Q Γ A (f , p) i j γ k)))
\end{code}

\begin{code}
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
\end{code}

\begin{code}
primrec₁₁' : ∀ P Q A i
  → (f : (j : Size< (↑ i)) → PSh.Obj (eval P (μ P ⊗ A)) j → PSh.Obj A j)
  → (p : (j : Size< (↑ i)) (k : Size< (↑ j)) (x : PSh.Obj (eval P (μ P ⊗ A)) j)
       → PSh.Mor A j k (f j x) ≡ f k (PSh.Mor (eval P (μ P ⊗ A)) j k x))
  → (j : Size< (↑ i)) → μObj' P Q j → PSh.Obj (eval Q (μ P ⊗ A)) j
primrec₁₂' : ∀ P Q A i
  → (f : (j : Size< (↑ i)) → PSh.Obj (eval P (μ P ⊗ A)) j → PSh.Obj A j)
  → (p : (j : Size< (↑ i)) (k : Size< (↑ j)) (x : PSh.Obj (eval P (μ P ⊗ A)) j)
       → PSh.Mor A j k (f j x) ≡ f k (PSh.Mor (eval P (μ P ⊗ A)) j k x))
  → (j : Size< (↑ i)) (k : Size< (↑ j)) (x : μObj' P Q j)
  → PSh.Mor (eval Q (μ P ⊗ A)) j k (primrec₁₁' P Q A i f p j x) ≡ primrec₁₁' P Q A i f p k (μMor' P Q j k x)
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
\end{code}

\begin{code}
primrec₂' : (P Q : Poly) (Γ : Ctx tot) (A : Ty tot)
  → (f : Tm Γ (eval P (μ P ⊗ A) ⇒ A))
  → (i : Size) (j : Size< (↑ i)) (γ : PSh.Obj Γ i)
  → (k : Size< (↑ j)) (x : μObj' P Q k)
  → primrec₁₁' P Q A i (proj₁ (proj₁ f i γ)) (proj₂ (proj₁ f i γ)) k x ≡
    primrec₁₁' P Q A j (proj₁ (proj₁ f j (PSh.Mor Γ i j γ))) (proj₂ (proj₁ f j (PSh.Mor Γ i j γ))) k x
primrec₂' P (∁ X) Γ A f i j γ k (∁ x) = refl
primrec₂' P I Γ A (f , p) i j γ k (I x) = cong (_,_ _) (cong₂ (λ a b → proj₁ a k b) (p i j γ) (primrec₂' P P Γ A (f , p) i j γ k x))
primrec₂' P (Q ⊠ R) Γ A f i j γ k (x ⊠ y) = cong₂ _,_ (primrec₂' P Q Γ A f i j γ k x) (primrec₂' P R Γ A f i j γ k y)
primrec₂' P (Q ⊞ R) Γ A f i j γ k (⊞₁ x) = cong inj₁ (primrec₂' P Q Γ A f i j γ k x)
primrec₂' P (Q ⊞ R) Γ A f i j γ k (⊞₂ x) = cong inj₂ (primrec₂' P R Γ A f i j γ k x)
primrec₂' P (► Q) Γ A f i j γ k (► x q) =
  Σ≡-uip (funext (λ { [ _ ] → funext (λ { [ _ ] → uip }) })) (funext (λ { [ l ] → primrec₂' P Q Γ A f i j γ l (x [ l ]) }))
\end{code}

\begin{code}
primrec' : ∀ P Q Γ A → Tm Γ (eval P (μ P ⊗ A) ⇒ A) → Tm Γ (μ' P Q ⇒ eval Q (μ P ⊗ A))
proj₁ (proj₁ (primrec' P Q Γ A (f , p)) i γ) j x = primrec₁₁' P Q A i (proj₁ (f i γ)) (proj₂ (f i γ)) j x
proj₂ (proj₁ (primrec' P Q Γ A (f , p)) i γ) j k x = primrec₁₂' P Q A i (proj₁ (f i γ)) (proj₂ (f i γ)) j k x
proj₂ (primrec' P Q Γ A (f , p)) i j γ =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ k → funext (primrec₂' P Q Γ A (f , p) i j γ k)))
\end{code}

\begin{code}
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
\end{code}
