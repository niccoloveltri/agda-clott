\AgdaHide{
\begin{code}
module CloTT.Structure.DefinitionalEquality where

open import Data.Product
open import Prelude
open import Presheaves
open import CloTT.Structure.Contexts
open import CloTT.Structure.Types
open import CloTT.Structure.Terms
\end{code}

\begin{code}
def-eq : {b : tag} (Γ : Ctx b) (A : Ty b) (s t : Tm Γ A) → Set
def-eq {set} Γ A s t = (x : _) → s x ≡ t x
def-eq {tot} Γ A (s , _) (t , _) = (i : Size) (x : _) → s i x ≡ t i x
\end{code}

\begin{code}
refl-def-eq : {b : tag} {Γ : Ctx b} {A : Ty b} {t : Tm Γ A}
  → def-eq Γ A t t
refl-def-eq {set} γ = refl
refl-def-eq {tot} i γ = refl

sym-def-eq : {b : tag} {Γ : Ctx b} {A : Ty b} {s t : Tm Γ A}
  → def-eq Γ A s t → def-eq Γ A t s
sym-def-eq {set} p γ = sym (p γ)
sym-def-eq {tot} p i γ = sym (p i γ)

trans-def-eq : {b : tag} {Γ : Ctx b} {A : Ty b} {s t u : Tm Γ A}
  → def-eq Γ A s t → def-eq Γ A t u → def-eq Γ A s u
trans-def-eq {set} p q γ = trans (p γ) (q γ)
trans-def-eq {tot} p q i γ = trans (p i γ) (q i γ)

eq-to-def-eq : {b : tag} {Γ : Ctx b} {A : Ty b} {s t : Tm Γ A}
  → s ≡ t → def-eq Γ A s t
eq-to-def-eq refl = refl-def-eq

def-eq-to-eq : {b : tag} {Γ : Ctx b} {A : Ty b} {s t : Tm Γ A}
  → def-eq Γ A s t → s ≡ t
def-eq-to-eq {set} p = funext p
def-eq-to-eq {tot} p =
  Σ≡-uip
    (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
    (funext (λ i → funext (λ x → p i x))) 
\end{code}
