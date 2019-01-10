\AgdaHide{
\begin{code}
module CloTT.Structure.DefinitionalEquality where

open import Data.Product
open import Prelude
open import Presheaves
open import CloTT.Structure.ClockContexts
open import CloTT.Structure.Contexts
open import CloTT.Structure.Types
open import CloTT.Structure.Terms
open import CloTT.Structure.Subst

open PSh
\end{code}
}

\begin{code}
def-eq : {b : tag} (Γ : Ctx b) (A : Ty b) (s t : Tm Γ A) → Set
def-eq {set} Γ A s t = (x : Γ) → s x ≡ t x
def-eq {tot} Γ A (s , p) (t , q) = (i : Size) (x : Obj Γ i) → s i x ≡ t i x
\end{code}

\AgdaHide{
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
    (funext (λ x → funext (λ y → funext (λ z → uip))))
    (funext (λ i → funext (λ x → p i x)))

eq-to-def-eq-to-eq : {b : tag} {Γ : Ctx b} {A : Ty b} {s t : Tm Γ A}
  → (p : def-eq Γ A s t) → eq-to-def-eq(def-eq-to-eq p) ≡ p
eq-to-def-eq-to-eq {set} p = funext (λ _ → uip)
eq-to-def-eq-to-eq {tot} p = funext (λ _ → funext (λ _ → uip))

def-eq-to-eq-to-def-eq : {b : tag} {Γ : Ctx b} {A : Ty b} {s t : Tm Γ A}
  → (p : s ≡ t) → def-eq-to-eq(eq-to-def-eq p) ≡ p
def-eq-to-eq-to-def-eq p = uip
\end{code}
}

\begin{code}
subst-eq : {b : tag} (Γ Γ' : Ctx b) (s t : sem-subst Γ Γ') → Set
subst-eq {set} Γ Γ' s t = (x : Γ) → s x ≡ t x
subst-eq {tot} Γ Γ' s t = (i : Size) (x : Obj Γ i) → proj₁ s i x ≡ proj₁ t i x
\end{code}

\AgdaHide{
\begin{code}
refl-subst-eq : {b : tag} {Γ Γ' : Ctx b} {s : sem-subst Γ Γ'}
  → subst-eq Γ Γ' s s
refl-subst-eq {set} x = refl
refl-subst-eq {tot} i x = refl

sym-subst-eq : {b : tag} {Γ Γ' : Ctx b} {s t : sem-subst Γ Γ'}
  → subst-eq Γ Γ' s t → subst-eq Γ Γ' t s
sym-subst-eq {set} p γ = sym (p γ)
sym-subst-eq {tot} p i γ = sym (p i γ)

trans-subst-eq : {b : tag} {Γ Γ' : Ctx b} {s t u : sem-subst Γ Γ'}
  → subst-eq Γ Γ' s t → subst-eq Γ Γ' t u → subst-eq Γ Γ' s u
trans-subst-eq {set} p q γ = trans (p γ) (q γ)
trans-subst-eq {tot} p q i γ = trans (p i γ) (q i γ)

eq-to-subst-eq : {b : tag} {Γ Γ' : Ctx b} {s t : sem-subst Γ Γ'}
  → s ≡ t → subst-eq Γ Γ' s t
eq-to-subst-eq refl = refl-subst-eq

subst-eq-to-eq : {b : tag} {Γ Γ' : Ctx b} {s t : sem-subst Γ Γ'}
  → subst-eq Γ Γ' s t → s ≡ t
subst-eq-to-eq {set} p = funext p
subst-eq-to-eq {tot} p =
  Σ≡-uip
    (funext (λ x → funext (λ y → funext (λ z → uip))))
    (funext (λ i → funext (λ x → p i x)))

subst-eq-to-eq-to-subst-eq : {b : tag} {Γ Γ' : Ctx b} {s t : sem-subst Γ Γ'}
  → (p : s ≡ t)
  → subst-eq-to-eq(eq-to-subst-eq p) ≡ p
subst-eq-to-eq-to-subst-eq p = uip

eq-to-subst-eq-to-eq : {b : tag} {Γ Γ' : Ctx b} {s t : sem-subst Γ Γ'}
  → (p : subst-eq Γ Γ' s t)
  → eq-to-subst-eq(subst-eq-to-eq p) ≡ p
eq-to-subst-eq-to-eq {set} p = funext (λ _ → uip)
eq-to-subst-eq-to-eq {tot} p = funext (λ _ → funext (λ _ → uip))
\end{code}
}
