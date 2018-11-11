{-
The function type.
-}
module CloTT.TypeFormers.FunctionType where

open import Data.Product
open import Prelude
open import Presheaves
open import CloTT.Structure

-- Formation rule
_⇒_ : {b : Bool} (A B : Ty b) → Ty b
_⇒_ {set} A B = A → B
_⇒_ {tot} A B = Exp A B

-- Introduction rule
lambda : {b : Bool} (Γ : Ctx b) (A B : Ty b) (t : Tm b (Γ ,, A) B) → Tm b Γ (A ⇒ B)
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

-- Elimination rule
app : {b : Bool} {Γ : Ctx b} {A B : Ty b} (f : Tm b Γ (A ⇒ B)) (t : Tm b Γ A) → Tm b Γ B
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

-- Computation rule
beta : {b : Bool} {Γ : Ctx b} {A B : Ty b} (t : Tm b (Γ ,, A) B) (x : Tm b Γ A)
     → def-eq Γ B (app {b} {Γ} {A} {B} (lambda Γ A B t) x) (subst-Tm {_} {Γ} {A} {B} t x)
beta {set} t x _ = refl
beta {tot} {Γ} (t , p) (x , q) Δ z = cong (λ z → t Δ (z , _)) ΓMorId
  where open PSh Γ renaming (MorId to ΓMorId)

eta : {b : Bool} {Γ : Ctx b} {A B : Ty b} (t : Tm b Γ (A ⇒ B))
  → def-eq Γ (A ⇒ B)
           (lambda Γ A B (app {_} {Γ ,, A} {A} {B} (weaken Γ A (A ⇒ B) t) (var Γ A)))
           t
eta {set} t x = refl
eta {tot} (t , p) Δ x =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ Δ' → funext (λ z → sym (cong (λ h → proj₁ h _ z) (p Δ Δ' x)))))

-- Identity and composition
{-
id-tm : {b : Bool} (Γ : Ctx b) (A : Ty b) → Tm b Γ (A ⇒ A)
id-tm {set} Γ A _ = id
proj₁ (proj₁ (id-tm {tot} Γ A) i γ) j = id
proj₂ (proj₁ (id-tm {tot} Γ A) i γ) j k x = refl
proj₂ (id-tm {tot} Γ A) i j γ = refl
-}

id-tm : {b : Bool} (Γ : Ctx b) (A : Ty b) → Tm b Γ (A ⇒ A)
id-tm Γ A = lambda Γ A A (var Γ A)

comp-tm : {b : Bool} (Γ : Ctx b) (A B C : Ty b)
  → Tm b Γ ((B ⇒ C) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
comp-tm Γ A B C = lambda Γ (B ⇒ C) ((A ⇒ B) ⇒ (A ⇒ C))
                         (lambda (Γ ,, (B ⇒ C)) (A ⇒ B) (A ⇒ C)
                                 (lambda ((Γ ,, (B ⇒ C)) ,, (A ⇒ B)) A C (app {_} {((Γ ,, (B ⇒ C)) ,, (A ⇒ B)) ,, A} {B} {C}
                                             (weaken ((Γ ,, (B ⇒ C)) ,, (A ⇒ B)) A (B ⇒ C) (weaken (Γ ,, (B ⇒ C)) (A ⇒ B) (B ⇒ C) (var Γ (B ⇒ C))))
                                             (app {_} {((Γ ,, (B ⇒ C)) ,, (A ⇒ B)) ,, A} {A} {B} (weaken ((Γ ,, (B ⇒ C)) ,, (A ⇒ B)) A (A ⇒ B) (var (Γ ,, (B ⇒ C)) (A ⇒ B)))
                                                                                                  (var (((Γ ,, (B ⇒ C)) ,, (A ⇒ B))) A)))))

{-
comp-tm : {b : Bool} (Γ : Ctx b) (A B C : Ty b)
  → Tm b Γ ((B ⇒ C) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
comp-tm {set} Γ A B C γ g f x = g (f x)
proj₁ (proj₁ (proj₁ (proj₁ (comp-tm {tot} Γ A B C) i γ) j (g , p)) k (f , q)) l x = g l (f l x)
proj₂ (proj₁ (proj₁ (proj₁ (comp-tm {tot} Γ A B C) i γ) j (g , p)) k (f , q)) l m x =
  begin
    PSh.Mor C l m (g l (f l x))
  ≡⟨ p l m (f l x) ⟩
    g m (PSh.Mor B l m (f l x))
  ≡⟨ cong (g m) (q l m x) ⟩
    g m (f m (PSh.Mor A l m x))
  ∎
proj₂ (proj₁ (proj₁ (comp-tm {tot} Γ A B C) i γ) j (g , p)) k l (f , q) = refl
proj₂ (proj₁ (comp-tm {tot} Γ A B C) i γ) j k (g , p) = refl
proj₂ (comp-tm {tot} Γ A B C) i j γ = refl
-}

{-
comp : {b : Bool} (Γ : Ctx b) (A B C : Ty b)
  → Tm b Γ (B ⇒ C) → Tm b Γ (A ⇒ B) → Tm b Γ (A ⇒ C)
comp {set} Γ A B C g f γ x = g γ (f γ x)
proj₁ (proj₁ (comp {tot} Γ A B C (g , p) (f , q)) i γ) j x = proj₁ (g i γ) j (proj₁ (f j (PSh.Mor Γ i j γ)) j x)
proj₂ (proj₁ (comp {tot} Γ A B C (g , p) (f , q)) i γ) j k x =
  begin
    PSh.Mor C j k (proj₁ (g i γ) j (proj₁ (f j (PSh.Mor Γ i j γ)) j x))
  ≡⟨ proj₂ (g i γ) j k (proj₁ (f j (PSh.Mor Γ i j γ)) j x) ⟩ 
    proj₁ (g i γ) k (PSh.Mor B j k (proj₁ (f j (PSh.Mor Γ i j γ)) j x))
  ≡⟨ cong (proj₁ (g i γ) k) (proj₂ (f j (PSh.Mor Γ i j γ)) j k x) ⟩ 
    proj₁ (g i γ) k (proj₁ (f j (PSh.Mor Γ i j γ)) k (PSh.Mor A j k x))
  ≡⟨ cong (λ a → proj₁ (g i γ) k (proj₁ a k (PSh.Mor A j k x))) (q j k (PSh.Mor Γ i j γ)) ⟩ 
    proj₁ (g i γ) k (proj₁ (f k (PSh.Mor Γ j k (PSh.Mor Γ i j γ))) k (PSh.Mor A j k x))
  ≡⟨ cong (λ a → proj₁ (g i γ) k (proj₁ (f k a) k (PSh.Mor A j k x))) (sym (PSh.MorComp Γ)) ⟩
    proj₁ (g i γ) k (proj₁ (f k (PSh.Mor Γ i k γ)) k (PSh.Mor A j k x))
  ∎
proj₂ (comp {tot} Γ A B C (g , p) (f , q)) i j γ =
  Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
         (funext (λ k → funext (λ x → cong₂ (λ a b → proj₁ a k (proj₁ (f k b) k x)) (p i j γ) (PSh.MorComp Γ))))
-}
