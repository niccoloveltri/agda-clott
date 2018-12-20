\AgdaHide{
\begin{code}
module CloTT.DefinitionalEqualities where

open import Data.Product
open import Prelude
open import Prelude.Syntax
open import Presheaves
open import CloTT.Structure
open import CloTT.TypeFormers
open import CloTT.InterpretSyntax

open PSh
\end{code}
}

\begin{code}

sem-λ-β : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t : Term (Γ , A) B) → def-eq _ _ ⟦ appTm (lambdaTm t) ⟧tm ⟦ t ⟧tm
sem-λ-β {∅} {Γ} {A} {B} t x = refl
sem-λ-β {κ} {Γ} {A} {B} t i x =
  begin
    proj₁ ⟦ t ⟧tm i (Mor ⟦ Γ ⟧Γ i i (proj₁ x) , proj₂ x)
  ≡⟨ cong (λ z → proj₁ ⟦ t ⟧tm i (z , _)) (MorId ⟦ Γ ⟧Γ) ⟩
    proj₁ ⟦ t ⟧tm i x
  ∎

sem-λ-η : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t : Term Γ (A ⟶ B)) → def-eq _ _ ⟦ lambdaTm (appTm t) ⟧tm ⟦ t ⟧tm
sem-λ-η {∅} {Γ} {A} {B} f x = refl
sem-λ-η {κ} {Γ} {A} {B} f i x =
  Σ≡-uip
    (funext (λ _ → funext (λ _ → funext (λ _ → uip))))
    (funext (λ j → cong (λ z → proj₁ z j) (sym (proj₂ ⟦ f ⟧tm i j x))))

sem-⊠-β₁ : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t₁ : Term Γ A) (t₂ : Term Γ B) → def-eq _ _ ⟦ π₁ [ t₁ & t₂ ] ⟧tm ⟦ t₁ ⟧tm
sem-⊠-β₁ {∅} {Γ} {A} {B} t₁ t₂ x = refl
sem-⊠-β₁ {κ} {Γ} {A} {B} t₁ t₂ i x = refl

sem-⊠-β₂ : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t₁ : Term Γ A) (t₂ : Term Γ B) → def-eq _ _ ⟦ π₂ [ t₁ & t₂ ] ⟧tm ⟦ t₂ ⟧tm
sem-⊠-β₂ {∅} {Γ} {A} {B} t₁ t₂ x = refl
sem-⊠-β₂ {κ} {Γ} {A} {B} t₁ t₂ i x = refl

sem-⊠-η : {Δ : ClockContext} {Γ : Context Δ} {A B : Type Δ} (t : Term Γ (A ⊠ B)) → def-eq _ _ ⟦ [ π₁ t & π₂ t ] ⟧tm ⟦ t ⟧tm
sem-⊠-η {∅} {Γ} {A} {B} t x = refl
sem-⊠-η {κ} {Γ} {A} {B} t i x = refl

sem-⊞-β₁ : {Δ : ClockContext} {Γ : Context Δ} {A B C : Type Δ} (l : Term (Γ , A) C) (r : Term (Γ , B) C) (t : Term Γ A)
  → def-eq _ _ ⟦ sub (⊞rec C l r) (idsub Γ ,s in₁ B t) ⟧tm ⟦ sub l (idsub Γ ,s t) ⟧tm
sem-⊞-β₁ {∅} {Γ} {A} {B} {C} l r t x = refl
sem-⊞-β₁ {κ} {Γ} {A} {B} {C} l r t i x = refl

sem-⊞-β₂ : {Δ : ClockContext} {Γ : Context Δ} {A B C : Type Δ} (l : Term (Γ , A) C) (r : Term (Γ , B) C) (t : Term Γ B)
  → def-eq _ _ ⟦ sub (⊞rec C l r) (idsub Γ ,s in₂ A t) ⟧tm ⟦ sub r (idsub Γ ,s t) ⟧tm
sem-⊞-β₂ {∅} {Γ} {A} {B} {C} l r t x = refl
sem-⊞-β₂ {κ} {Γ} {A} {B} {C} l r t i x = refl

sem-𝟙-β : {Γ : Context ∅} {A : Type ∅} (t : Term Γ A) → def-eq _ _ ⟦ sub (unit-rec t) (idsub Γ ,s tt) ⟧tm ⟦ t ⟧tm
sem-𝟙-β {Γ} {A} t x = refl

sem-𝟙-η : {Γ : Context ∅} (t : Term Γ 𝟙) → def-eq ⟦ Γ ⟧Γ ⟦ 𝟙 ⟧A ⟦ t ⟧tm ⟦ tt {Γ} ⟧tm
sem-𝟙-η t x = refl

sem-□-β : {Γ : Context ∅} {A : Type κ} (t : Term (weakenC Γ) A) → def-eq ⟦ weakenC Γ ⟧Γ ⟦ A ⟧A ⟦ unbox-q (box-q t) ⟧tm ⟦ t ⟧tm
sem-□-β {Γ} {A} t i x = refl

sem-□-η : {Γ : Context ∅} {A : Type κ} (t : Term Γ (clock-q A)) → def-eq ⟦ Γ ⟧Γ ⟦ clock-q A ⟧A ⟦ box-q (unbox-q t) ⟧tm ⟦ t ⟧tm
sem-□-η t x = refl

sem-next-id : {Γ : Context κ} {A : Type κ} (t : Term Γ (later A)) → def-eq ⟦ Γ ⟧Γ ⟦ later A ⟧A ⟦ next (idmap A) ⊛ t ⟧tm ⟦ t ⟧tm
sem-next-id t i x =
  Σ≡-uip
    (funext (λ { [ _ ] → funext (λ { [ _ ] → uip })}))
    (funext (λ { [ j ] → refl }))

sem-next-⊛ : {Γ : Context κ} {A B : Type κ} (f : Term Γ (A ⟶ B)) (t : Term Γ A) → def-eq ⟦ Γ ⟧Γ ⟦ later B ⟧A ⟦ next f ⊛ next t ⟧tm ⟦ next (app-map f t) ⟧tm
sem-next-⊛ f t i x =
  Σ≡-uip
    (funext (λ { [ _ ] → funext (λ { [ _ ] → uip })}))
    (funext (λ { [ j ] → refl }))

sem-next-comp : {Γ : Context κ} {A B C : Type κ} (g : Term Γ (later (B ⟶ C))) (f : Term Γ (later (A ⟶ B))) (t : Term Γ (later A))
  → def-eq ⟦ Γ ⟧Γ ⟦ later C ⟧A ⟦ ((next compmap ⊛ g) ⊛ f) ⊛ t  ⟧tm ⟦ g ⊛ (f ⊛ t) ⟧tm
sem-next-comp g f t i x =
  Σ≡-uip (funext (λ { [ _ ] → funext (λ { [ _ ] → uip })}))
         (funext (λ { [ j ] → refl}))

sem-next-λ : {Γ : Context κ} {A B : Type κ} (f : Term Γ (later (A ⟶ B))) (t : Term Γ A)
  → def-eq ⟦ Γ ⟧Γ ⟦ later B ⟧A ⟦ f ⊛ next t ⟧tm ⟦ next (lambdaTm (app-map (varTm _ _) (weakenTm _ _ _ t))) ⊛ f ⟧tm
sem-next-λ {Γ} f t i x =
  Σ≡-uip
    (funext (λ { [ _ ] → funext (λ { [ _ ] → uip })}))
    (funext (λ { [ j ] → cong (λ z → proj₁ (proj₁ (proj₁ ⟦ f ⟧tm i x) [ j ]) j (proj₁ ⟦ t ⟧tm j z)) (sym (MorId ⟦ Γ ⟧Γ))}))

dfix-eq : (Γ : Ctx tot) (A : Ty tot) (f : Tm Γ (▻ A ⇒ A))
  → def-eq {tot} Γ (▻ A) (dfix Γ A f) (pure Γ A (fix Γ A f))
dfix-eq Γ A (f , p) i γ =
  Σ≡-uip
    (funext (λ { [ j ] → funext (λ { [ k ] → uip }) }))
    (funext (λ { [ j ] → cong (λ a → proj₁ a j (dfix₁ A j (proj₁ a , proj₂ a))) (p i j γ)}))

fix-eq : (Γ : Ctx tot) (A : Ty tot) (f : Tm Γ (▻ A ⇒ A))
  → def-eq Γ A
           (fix Γ A f)
           (sem-app-map Γ (▻ A) A f (pure Γ A (fix Γ A f)))
fix-eq Γ A f i x = cong (proj₁ (proj₁ f i x) i) (dfix-eq Γ A f i x)

sem-fix-f : {Γ : Context κ} {A : Type κ} (f : Term Γ (later A ⟶ A))
  → def-eq ⟦ Γ ⟧Γ ⟦ A ⟧A
           ⟦ fix-tm f ⟧tm
           ⟦ app-map f (next (fix-tm f)) ⟧tm
sem-fix-f f = fix-eq _ _ ⟦ f ⟧tm

dfix-un : (Γ : Ctx tot) (A : Ty tot) (f : Tm Γ (▻ A ⇒ A)) (u : Tm Γ A) (i : Size) (x : Obj Γ i)
  → def-eq Γ A (sem-app-map Γ (▻ A) A f (pure Γ A u)) u
  → dfix₁ A i (proj₁ f i x) ≡ proj₁ (pure Γ A u) i x
dfix-un Γ A (f , p) (u , q) i x r =
  Σ≡-uip
    (funext (λ { [ j ] → funext (λ { [ k ] → uip }) }))
    (funext (λ {[ j ] →
      begin
        proj₁ (f i x) j (dfix₁ A j (proj₁ (f i x) , proj₂ (f i x)))
      ≡⟨ cong (λ z → proj₁ z j (dfix₁ A j z)) (p i j x) ⟩
        proj₁ (f j (Mor Γ i j x)) j (dfix₁ A j (f j (Mor Γ i j x)))
      ≡⟨ cong (proj₁ (f j (Mor Γ i j x)) j) (dfix-un Γ A (f , p) (u , q) j (Mor Γ i j x) r) ⟩
        proj₁ (f j (Mor Γ i j x)) j (proj₁ (pure Γ A (u , q)) j (Mor Γ i j x))
      ≡⟨ r j (Mor Γ i j x) ⟩
        u j (Mor Γ i j x)
      ∎
    }))

fix-un : (Γ : Ctx tot) (A : Ty tot) (f : Tm Γ (▻ A ⇒ A)) (u : Tm Γ A)
  → def-eq Γ A (sem-app-map Γ (▻ A) A f (pure Γ A u)) u
  → def-eq Γ A (fix Γ A f) u
fix-un Γ A f u p i x =
  begin
    proj₁ (fix Γ A f) i x
  ≡⟨ cong (λ z → proj₁ (proj₁ f i x) i z) (dfix-un Γ A f u i x p) ⟩
    proj₁ (sem-app-map Γ (▻ A) A f (pure Γ A u)) i x
  ≡⟨ p i x ⟩
    proj₁ u i x
  ∎

sem-fix-u : {Γ : Context κ} {A : Type κ} (f : Term Γ (later A ⟶ A)) (u : Term Γ A)
  → def-eq ⟦ Γ ⟧Γ ⟦ A ⟧A
           ⟦ app-map f (next u) ⟧tm
           ⟦ u ⟧tm
  → def-eq ⟦ Γ ⟧Γ ⟦ A ⟧A
           ⟦ fix-tm f ⟧tm
           ⟦ u ⟧tm
sem-fix-u f u p = fix-un _ _ ⟦ f ⟧tm ⟦ u ⟧tm p
\end{code}
