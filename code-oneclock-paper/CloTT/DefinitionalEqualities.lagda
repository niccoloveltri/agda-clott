\AgdaHide{
\begin{code}
module CloTT.DefinitionalEqualities where

open import Data.Product
open import Data.Sum
open import Data.Unit
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

sem-⇡-β : {Γ : Context ∅} {A : Type ∅} (t : Term Γ A) → def-eq ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ ↓ (⇡ t) ⟧tm ⟦ t ⟧tm
sem-⇡-β t x = refl

sem-⇡-η : {Γ : Context ∅} {A : Type ∅} (t : Term (weakenC Γ) (weakenT A)) → def-eq ⟦ weakenC Γ ⟧Γ ⟦ weakenT A ⟧A ⟦ ⇡ (↓ t) ⟧tm ⟦ t ⟧tm
sem-⇡-η t = proj₂ ⟦ t ⟧tm ∞

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


mutual
{-
  ⟦_⟧tm-eq : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {t₁ t₂ : Term Γ A} → t₁ ∼ t₂ → def-eq ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ t₁ ⟧tm ⟦ t₂ ⟧tm
  ⟦_⟧tm-eq {∅} refl∼ x = refl
  ⟦_⟧tm-eq {∅} (sym∼ p) x = sym (⟦_⟧tm-eq {∅} p x)
  ⟦_⟧tm-eq {∅} (trans∼ p q) x = trans (⟦_⟧tm-eq {∅} p x) (⟦_⟧tm-eq {∅} q x)
  ⟦_⟧tm-eq {∅} (cong-sub {t₂ = t₂}{s₁} p q) x = trans (⟦_⟧tm-eq {∅} p (⟦ s₁ ⟧sub x)) (cong ⟦ t₂ ⟧tm (⟦ q ⟧sub-eq x))
  ⟦_⟧tm-eq {∅} (cong-unit-rec p) (x , tt) = ⟦ p ⟧tm-eq x
  ⟦_⟧tm-eq {∅} (cong-in₁ B p) x = cong inj₁ (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq {∅} (cong-in₂ A p) x = cong inj₂ (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq {∅} (cong-⊞rec C p q) (x , inj₁ a) = ⟦ p ⟧tm-eq (x , a)
  ⟦_⟧tm-eq {∅} (cong-⊞rec C p q) (x , inj₂ b) = ⟦ q ⟧tm-eq (x , b)
  ⟦_⟧tm-eq {∅} cong-[ p & q ] x = cong₂ _,_ (⟦ p ⟧tm-eq x) (⟦ q ⟧tm-eq x)
  ⟦_⟧tm-eq {∅} (cong-π₁ p) x = cong proj₁ (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq {∅} (cong-π₂ p) x = cong proj₂ (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq {∅} (cong-lambdaTm p) x = funext (λ a → ⟦ p ⟧tm-eq (x , a))
  ⟦_⟧tm-eq {∅} (cong-appTm p) (x , a) = cong (λ z → z a) (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq {∅} (cong-↓ p) x = ⟦ p ⟧tm-eq ∞ x
  ⟦_⟧tm-eq {∅} (cong-box-q p) x = Σ≡-uip (funext (λ _ → funext (λ _ → uip))) (funext (λ i → ⟦ p ⟧tm-eq i x))
  ⟦_⟧tm-eq {∅} (λ-β t) = sem-λ-β t
  ⟦_⟧tm-eq {∅} (λ-η t) = sem-λ-η t
  ⟦_⟧tm-eq {∅} (⊠-β₁ t₁ t₂) = sem-⊠-β₁ t₁ t₂
  ⟦_⟧tm-eq {∅} (⊠-β₂ t₁ t₂) = {!!}
  ⟦_⟧tm-eq {∅} (⊠-η t) = {!!}
  ⟦_⟧tm-eq {∅} (⊞-β₁ l r t) = {!!}
  ⟦_⟧tm-eq {∅} (⊞-β₂ l r t) = {!!}
  ⟦_⟧tm-eq {∅} (𝟙-β t) = {!!}
  ⟦_⟧tm-eq {∅} (𝟙-η t) = {!!}
  ⟦_⟧tm-eq {∅} (□-η t) = {!!}
  ⟦_⟧tm-eq {∅} (⇡-β t) = {!!}
  ⟦_⟧tm-eq {κ} p = {!!}
-}

  ⟦_⟧tm-eq : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} {t₁ t₂ : Term Γ A} → t₁ ∼ t₂ → def-eq ⟦ Γ ⟧Γ ⟦ A ⟧A ⟦ t₁ ⟧tm ⟦ t₂ ⟧tm
  ⟦_⟧tm-eq {∅} refl∼ x = refl
  ⟦_⟧tm-eq {κ} refl∼ i x = refl
  ⟦_⟧tm-eq {∅} (sym∼ p) x = sym (⟦_⟧tm-eq p x)
  ⟦_⟧tm-eq {κ} (sym∼ p) i x = sym (⟦_⟧tm-eq p i x)
  ⟦_⟧tm-eq {∅} (trans∼ p q) x = trans (⟦_⟧tm-eq p x) (⟦_⟧tm-eq q x)
  ⟦_⟧tm-eq {κ} (trans∼ p q) i x = trans (⟦_⟧tm-eq p i x) (⟦_⟧tm-eq q i x)
  ⟦_⟧tm-eq {∅} (cong-sub {t₂ = t₂} {s₁} p q) x = trans (⟦_⟧tm-eq p (⟦ s₁ ⟧sub x)) (cong ⟦ t₂ ⟧tm (⟦ q ⟧sub-eq x))
  ⟦_⟧tm-eq {κ} (cong-sub {t₂ = t₂} {s₁} p q) i x = trans (⟦_⟧tm-eq p i (proj₁ ⟦ s₁ ⟧sub i x)) (cong (proj₁ ⟦ t₂ ⟧tm i) (⟦ q ⟧sub-eq i x))
  ⟦ cong-unit-rec p ⟧tm-eq (x , tt) = ⟦ p ⟧tm-eq x
  ⟦_⟧tm-eq {∅} (cong-in₁ B p) x = cong inj₁ (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq {κ} (cong-in₁ B p) i x = cong inj₁ (⟦ p ⟧tm-eq i x)
  ⟦_⟧tm-eq {∅} (cong-in₂ A p) x = cong inj₂ (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq {κ} (cong-in₂ A p) i x = cong inj₂ (⟦ p ⟧tm-eq i x)
  ⟦_⟧tm-eq {∅} (cong-⊞rec C p q) (x , inj₁ a) = ⟦ p ⟧tm-eq (x , a) 
  ⟦_⟧tm-eq {∅} (cong-⊞rec C p q) (x , inj₂ b) = ⟦ q ⟧tm-eq (x , b) 
  ⟦_⟧tm-eq {κ} (cong-⊞rec C p q) i (x , inj₁ a) = ⟦ p ⟧tm-eq i (x , a)
  ⟦_⟧tm-eq {κ} (cong-⊞rec C p q) i (x , inj₂ b) = ⟦ q ⟧tm-eq i (x , b)
  ⟦_⟧tm-eq {∅} cong-[ p & q ] x = cong₂ _,_ (⟦ p ⟧tm-eq x) (⟦ q ⟧tm-eq x)
  ⟦_⟧tm-eq {κ} cong-[ p & q ] i x = cong₂ _,_ (⟦ p ⟧tm-eq i x) (⟦ q ⟧tm-eq i x)
  ⟦_⟧tm-eq {∅} (cong-π₁ p) x = cong proj₁ (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq {κ} (cong-π₁ p) i x = cong proj₁ (⟦ p ⟧tm-eq i x)
  ⟦_⟧tm-eq {∅} (cong-π₂ p) x = cong proj₂ (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq {κ} (cong-π₂ p)  i x = cong proj₂ (⟦ p ⟧tm-eq i x)
  ⟦_⟧tm-eq {∅} (cong-lambdaTm p) x = funext (λ a → ⟦ p ⟧tm-eq (x , a))
  ⟦_⟧tm-eq {κ} (cong-lambdaTm {Γ = Γ} p) i x =
    Σ≡-uip (funext (λ _ → funext (λ _ → funext (λ _ → uip)))) (funext (λ j → funext (λ a → ⟦ p ⟧tm-eq j (Mor ⟦ Γ ⟧Γ i j x , a))))
  ⟦_⟧tm-eq {∅} (cong-appTm p) (x , a) = cong (λ z → z a) (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq {κ} (cong-appTm p) i (x , a) = cong (λ z → proj₁ z i a) (⟦ p ⟧tm-eq i x)
  ⟦ cong-⇡ p ⟧tm-eq i x = ⟦ p ⟧tm-eq x
  ⟦ cong-↓ p ⟧tm-eq x = ⟦ p ⟧tm-eq ∞ x
  ⟦ cong-box-q p ⟧tm-eq x = Σ≡-uip (funext (λ _ → funext (λ _ → uip))) (funext (λ i → ⟦ p ⟧tm-eq i x))
  ⟦ cong-unbox-q p ⟧tm-eq i x = cong (λ z → proj₁ z i) (⟦ p ⟧tm-eq x)
  ⟦_⟧tm-eq (cong-next {Γ = Γ} p) i x =
    Σ≡-uip (funext (λ { [ _ ] → funext (λ { [ _ ] → uip }) })) (funext (λ{ [ j ] → ⟦ p ⟧tm-eq j (Mor ⟦ Γ ⟧Γ i j x) }))
  ⟦_⟧tm-eq (cong- p ⊛ q) i x =
    Σ≡-uip (funext (λ { [ _ ] → funext (λ { [ _ ] → uip }) }))
           (funext (λ{ [ j ] → cong₂ (λ a b → proj₁ (proj₁ a [ j ]) j (proj₁ b [ j ])) (⟦ p ⟧tm-eq i x) (⟦ q ⟧tm-eq i x) }))
  ⟦_⟧tm-eq (cong-fix-tm {A = A} p) i x = cong (λ z → proj₁ z i (dfix₁ ⟦ A ⟧A i z)) (⟦ p ⟧tm-eq i x)
  ⟦ λ-β t ⟧tm-eq = sem-λ-β t
  ⟦ λ-η t ⟧tm-eq = sem-λ-η t
  ⟦ ⊠-β₁ t₁ t₂ ⟧tm-eq = sem-⊠-β₁ t₁ t₂
  ⟦ ⊠-β₂ t₁ t₂ ⟧tm-eq = sem-⊠-β₂ t₁ t₂
  ⟦ ⊠-η t ⟧tm-eq = sem-⊠-η t
  ⟦ ⊞-β₁ l r t ⟧tm-eq = sem-⊞-β₁ l r t
  ⟦ ⊞-β₂ l r t ⟧tm-eq = sem-⊞-β₂ l r t
  ⟦ 𝟙-β t ⟧tm-eq = sem-𝟙-β t
  ⟦ 𝟙-η t ⟧tm-eq = sem-𝟙-η t
  ⟦ □-β t ⟧tm-eq = sem-□-β t
  ⟦ □-η t ⟧tm-eq = sem-□-η t
  ⟦ ⇡-β t ⟧tm-eq = sem-⇡-β t
  ⟦ ⇡-η t ⟧tm-eq = sem-⇡-η t
  ⟦ next-id t ⟧tm-eq = sem-next-id t
  ⟦ next-comp g f t ⟧tm-eq = sem-next-comp g f t
  ⟦ next-⊛ f t ⟧tm-eq = sem-next-⊛ f t
  ⟦ next-λ f t ⟧tm-eq = sem-next-λ f t
  ⟦ fix-f f ⟧tm-eq = sem-fix-f f
  ⟦ fix-u f u p ⟧tm-eq = sem-fix-u f u ⟦ p ⟧tm-eq

  ⟦_⟧sub-eq : {Δ : ClockContext} {Γ Γ' : Context Δ} {s₁ s₂ : Subst Γ Γ'} → s₁ ≈ s₂ → subst-eq _ _ ⟦ s₁ ⟧sub ⟦ s₂ ⟧sub
  ⟦_⟧sub-eq {Δ} p = {!!}

sem-sub-idl : {Δ : ClockContext} {Γ Γ' : Context Δ} (s : Subst Γ Γ') → subst-eq _ _ ⟦ idsub Γ' o s ⟧sub ⟦ s ⟧sub
sem-sub-idl {∅} s x = refl
sem-sub-idl {κ} s i x = refl

sem-sub-idr : {Δ : ClockContext} {Γ Γ' : Context Δ} (s : Subst Γ Γ') → subst-eq _ _ ⟦ s o idsub Γ ⟧sub ⟦ s ⟧sub
sem-sub-idr {∅} s x = refl
sem-sub-idr {κ} s i x = refl

sem-sub-assoc : {Δ : ClockContext} {Γ₁ Γ₂ Γ₃ Γ₄ : Context Δ} (s₁ : Subst Γ₁ Γ₂) (s₂ : Subst Γ₂ Γ₃) (s₃ : Subst Γ₃ Γ₄)
  → subst-eq _ _ ⟦ s₃ o (s₂ o s₁) ⟧sub ⟦ (s₃ o s₂) o s₁ ⟧sub
sem-sub-assoc {∅} s₁ s₂ s₃ x = refl
sem-sub-assoc {κ} s₁ s₂ s₃ i x = refl

sem-sub-π₁β : {Δ : ClockContext} {Γ Γ' : Context Δ} {A : Type Δ} {t : Term Γ A} (s : Subst Γ Γ')
  → subst-eq _ _ ⟦ pr (s ,s t) ⟧sub ⟦ s ⟧sub
sem-sub-π₁β {∅} s x = refl
sem-sub-π₁β {κ} s i x = refl

sem-sub-εη : {Δ : ClockContext} {Γ : Context Δ} (s : Subst Γ •) → subst-eq _ _ ⟦ s ⟧sub ⟦ ε Γ ⟧sub
sem-sub-εη {∅} s x = refl
sem-sub-εη {κ} s i x = refl

sem-sub-,o : {Δ : ClockContext} {Γ₁ Γ₂ Γ₃ : Context Δ} {A : Type Δ} {t : Term Γ₂ A} (s₁ : Subst Γ₁ Γ₂) (s₂ : Subst Γ₂ Γ₃)
  → subst-eq _ _ ⟦ (s₂ ,s t) o s₁ ⟧sub ⟦ (s₂ o s₁) ,s sub t s₁ ⟧sub
sem-sub-,o {∅} s₁ s₂ x = refl
sem-sub-,o {κ} s₁ s₂ i x = refl

sem-sub-η : {Δ : ClockContext} {Γ : Context Δ} {A : Type Δ} (s : Subst Γ (Γ , A))
  → subst-eq _ _ ⟦ pr s ,s sub (varTm Γ A) s ⟧sub ⟦ s ⟧sub
sem-sub-η {∅} s x = refl
sem-sub-η {κ} s i x = refl
\end{code}
