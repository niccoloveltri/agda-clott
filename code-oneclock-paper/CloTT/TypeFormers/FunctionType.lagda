\AgdaHide{
\begin{code}
module CloTT.TypeFormers.FunctionType where

open import Data.Product
open import Prelude
open import Presheaves
open import CloTT.Structure
\end{code}
}

\begin{code}
_⇒_ : {b : tag} (A B : Ty b) → Ty b
_⇒_ {set} A B = A → B
_⇒_ {tot} A B = Exp A B
\end{code}

\begin{code}
lambda : {b : tag} (Γ : Ctx b) (A B : Ty b) (t : Tm b (Γ ,, A) B) → Tm b Γ (A ⇒ B)
lambda {set} Γ A B t x y = t (x , y)
proj₁ (proj₁ (lambda {tot} Γ A B (t , p)) i x) j z = t j (ΓMor i j x , z)
  where open PSh Γ renaming (Mor to ΓMor;MorComp to ΓMorComp)
proj₂ (proj₁ (lambda {tot} Γ A B (t , p)) i x) j k y =
  begin
    PSh.Mor B j k (t j (ΓMor i j x , y))
  ≡⟨ p j k (ΓMor i j x , y) ⟩
    t k (PSh.Mor (Γ ,, A) j k (ΓMor i j x , y))
  ≡⟨ cong (λ z → t k (z , _)) (sym ΓMorComp) ⟩
    t k (ΓMor i k x , PSh.Mor A j k y)
  ∎
  where open PSh Γ renaming (Mor to ΓMor;MorComp to ΓMorComp)
proj₂ (lambda {tot} Γ A B (t , p)) i j x =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ k → (funext (λ z → cong (λ z → t k (z , _)) ΓMorComp))))
  where open PSh Γ renaming (Mor to ΓMor;MorComp to ΓMorComp)
\end{code}

\begin{code}
app : {b : tag} {Γ : Ctx b} {A B : Ty b} (f : Tm b Γ (A ⇒ B)) (t : Tm b Γ A) → Tm b Γ B
app {set} f t x = f x (t x)
proj₁ (app {tot} {Γ} (f , p) (t , q)) i x = let (f' , _) = f i x in f' _ (t i x)
proj₂ (app {tot} {Γ} {A} {B} (f , p) (t , q)) i j x =
  let (f' , p') = f i x in
  begin
    PSh.Mor B i j (proj₁ (f i x) _ (t i x))
  ≡⟨ p' i j (t i x) ⟩
    proj₁ (f i x) j (PSh.Mor A i j (t i x))
  ≡⟨ cong₂ (λ z g → proj₁ g _ z) (q i j x) (p i j x) ⟩
    proj₁ (f j (PSh.Mor Γ i j x)) _ (t j (PSh.Mor Γ i j x))
  ∎
\end{code}

\begin{code}
beta : {b : tag} {Γ : Ctx b} {A B : Ty b} (t : Tm b (Γ ,, A) B) (x : Tm b Γ A)
     → def-eq Γ B (app {b} {Γ} {A} {B} (lambda Γ A B t) x) (subst-Tm {_} {Γ} {A} {B} t x)
beta {set} t x _ = refl
beta {tot} {Γ} (t , p) (x , q) Δ z = cong (λ z → t Δ (z , _)) ΓMorId
  where open PSh Γ renaming (MorId to ΓMorId)
\end{code}

\begin{code}
eta : {b : tag} {Γ : Ctx b} {A B : Ty b} (t : Tm b Γ (A ⇒ B))
  → def-eq Γ (A ⇒ B)
           (lambda Γ A B (app {_} {Γ ,, A} {A} {B} (weaken Γ A (A ⇒ B) t) (var Γ A)))
           t
eta {set} t x = refl
eta {tot} (t , p) Δ x =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ Δ' → funext (λ z → sym (cong (λ h → proj₁ h _ z) (p Δ Δ' x)))))
\end{code}

\begin{code}
id-tm : {b : tag} (Γ : Ctx b) (A : Ty b) → Tm b Γ (A ⇒ A)
id-tm Γ A = lambda Γ A A (var Γ A)
\end{code}

\begin{code}
comp-tm : {b : tag} (Γ : Ctx b) (A B C : Ty b)
  → Tm b Γ ((B ⇒ C) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
comp-tm Γ A B C = lambda Γ (B ⇒ C) ((A ⇒ B) ⇒ (A ⇒ C))
                         (lambda (Γ ,, (B ⇒ C)) (A ⇒ B) (A ⇒ C)
                                 (lambda ((Γ ,, (B ⇒ C)) ,, (A ⇒ B)) A C (app
                                             (weaken ((Γ ,, (B ⇒ C)) ,, (A ⇒ B)) A (B ⇒ C) (weaken (Γ ,, (B ⇒ C)) (A ⇒ B) (B ⇒ C) (var Γ (B ⇒ C))))
                                             (app (weaken ((Γ ,, (B ⇒ C)) ,, (A ⇒ B)) A (A ⇒ B) (var (Γ ,, (B ⇒ C)) (A ⇒ B)))
                                                  (var (((Γ ,, (B ⇒ C)) ,, (A ⇒ B))) A)))))
\end{code}
