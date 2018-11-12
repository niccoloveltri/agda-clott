{-
The function type.
-}
module CloTT.TypeFormers.FunctionType where

open import Data.Product
open import Prelude
open import Presheaves
open import CloTT.Structure

-- Formation rule
_⇒_ : {n : ℕ} (A B : Ty n) → Ty n
A ⇒ B = Exp A B

-- Introduction rule
lambda : {n : ℕ} (Γ : Ctx n) (A B : Ty n) (t : Tm (Γ ,, A) B) → Tm Γ (A ⇒ B)
proj₁ (proj₁ (lambda Γ A B (t , p)) Δ x) Δ' z = t Δ' (ΓMor Δ Δ' x , z)
  where open PSh Γ renaming (Mor to ΓMor;MorComp to ΓMorComp)
proj₂ (proj₁ (lambda Γ A B (t , p)) Δ x) Δ' Δ'' y =
  begin
    Ctx.Mor B Δ' _ (t Δ' (ΓMor Δ Δ' x , y))
  ≡⟨ p Δ' _ (ΓMor Δ Δ' x , y) ⟩
    t Δ'' (Ctx.Mor (Γ ,, A) Δ' _ (ΓMor Δ Δ' x , y))
  ≡⟨ cong (λ z → t Δ'' (z , _)) (sym ΓMorComp) ⟩
    t Δ'' (ΓMor Δ Δ'' x , Ctx.Mor A Δ' _ y)
  ∎
  where open PSh Γ renaming (Mor to ΓMor;MorComp to ΓMorComp)
proj₂ (lambda Γ A B (t , p)) Δ Δ' x =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ Δ'' → (funext (λ z → cong (λ z → t Δ'' (z , _)) ΓMorComp))))
  where open PSh Γ renaming (Mor to ΓMor;MorComp to ΓMorComp)

-- Elimination rule
app : {n : ℕ} {Γ : Ctx n} {A B : Ty n} (f : Tm Γ (A ⇒ B)) (t : Tm Γ A) → Tm Γ B
proj₁ (app {n} {Γ} (f , p) (t , q)) Δ x = let (f' , _) = f Δ x in f' _ (t Δ x)
proj₂ (app {n} {Γ} {A} {B} (f , p) (t , q)) Δ Δ' x =
  let (f' , p') = f Δ x in
  begin
    Ctx.Mor B Δ Δ' (proj₁ (f Δ x) _ (t Δ x))
  ≡⟨ p' _ _ (t Δ x) ⟩
    proj₁ (f Δ x) Δ' (Ctx.Mor A Δ Δ' (t Δ x))
  ≡⟨ cong₂ (λ z g → proj₁ g _ z) (q Δ Δ' x) (p Δ Δ' x) ⟩
    proj₁ (f Δ' (Ctx.Mor Γ Δ Δ' x)) _ (t Δ' (Ctx.Mor Γ Δ Δ' x))
  ∎

-- Computation rule
beta : {n : ℕ} {Γ : Ctx n} {A B : Ty n} (t : Tm (Γ ,, A) B) (x : Tm Γ A)
     → def-eq Γ B (app {n} {Γ} {A} {B} (lambda Γ A B t) x) (subst-Tm {_} {Γ} {A} {B} t x)
beta {n} {Γ} (t , p) (x , q) Δ z = cong (λ z → t Δ (z , _)) ΓMorId
  where open PSh Γ renaming (MorId to ΓMorId)

eta : {n : ℕ} {Γ : Ctx n} {A B : Ty n} (t : Tm Γ (A ⇒ B))
  → def-eq Γ (A ⇒ B)
           (lambda Γ A B (app {_} {Γ ,, A} {A} {B} (weaken Γ A (A ⇒ B) t) (var Γ A)))
           t
eta (t , p) Δ x =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ Δ' → funext (λ z → sym (cong (λ h → proj₁ h _ z) (p Δ Δ' x)))))

id-tm : {n : ℕ} (Γ : Ctx n) (A : Ty n) → Tm Γ (A ⇒ A)
id-tm Γ A = lambda Γ A A (var Γ A)

comp-tm : {n : ℕ} (Γ : Ctx n) (A B C : Ty n)
  → Tm Γ ((B ⇒ C) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
comp-tm Γ A B C = lambda Γ (B ⇒ C) ((A ⇒ B) ⇒ (A ⇒ C))
                         (lambda (Γ ,, (B ⇒ C)) (A ⇒ B) (A ⇒ C)
                                 (lambda ((Γ ,, (B ⇒ C)) ,, (A ⇒ B)) A C (app {_} {((Γ ,, (B ⇒ C)) ,, (A ⇒ B)) ,, A} {B} {C}
                                             (weaken ((Γ ,, (B ⇒ C)) ,, (A ⇒ B)) A (B ⇒ C) (weaken (Γ ,, (B ⇒ C)) (A ⇒ B) (B ⇒ C) (var Γ (B ⇒ C))))
                                             (app {_} {((Γ ,, (B ⇒ C)) ,, (A ⇒ B)) ,, A} {A} {B} (weaken ((Γ ,, (B ⇒ C)) ,, (A ⇒ B)) A (A ⇒ B) (var (Γ ,, (B ⇒ C)) (A ⇒ B)))
                                                                                                  (var (((Γ ,, (B ⇒ C)) ,, (A ⇒ B))) A)))))
