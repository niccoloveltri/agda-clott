module OneClockHeterogeneousEq where

open import Size
open import Level renaming (suc to lsuc)
open import Relation.Binary.HeterogeneousEquality
open import Function hiding (const)
open import Data.Product
open import Data.Nat hiding (_⊔_)


{- Clocked Type Theory in Agda via sized types -}

-- PS: This is a test version with heterogeneous equality instead of
-- the usual homogeneous propositional equality.

-- In this file we consider clock contexts containing only one
-- clock. This is just to set things right before generalizing to
-- multiple clocks.

-- A clock is a size. A tick on a clock κ is a size smaller than κ.

Clock = Size

Tick : Clock → Set
Tick κ = Size< κ

data _≤ˢ_ : Size → Size → Set where
  refl≤ˢ : {κ : Size} → κ ≤ˢ κ
  <-≤ˢ : {κ : Size} → (α : Size< κ) → α ≤ˢ κ

Size≤ : Clock → Set
Size≤ κ = Σ Size (λ α → α ≤ˢ κ)

Tick= : Clock → Set
Tick= κ = Size≤ κ

-- A context (or a closed type) is a presheaf over clocks. Notice
-- though that clocks form a preorder, not a poset.

record Ctx ℓ : Set (Level.suc ℓ) where
  constructor ctx
  field
    Γ : Clock → Set ℓ
    next : (κ : Clock)(α : Tick κ) → Γ κ → Γ α
    next-ass : (κ : Clock)(α : Tick κ)(β : Tick α)
      → (ρ : Γ κ) → next α β (next κ α ρ) ≅ next κ β ρ
open Ctx

ClTy = Ctx

-- Dependent types. As usual in presheaf semantics, a type in a
-- context Γ is a presheaf on the category of elements of Γ.

record Ty {ℓ} ℓ' (c : Ctx ℓ) : Set (lsuc (ℓ' ⊔ ℓ)) where
  constructor ty
  field
    A : (κ : Clock) → Γ c κ → Set ℓ'
    Ty-next : (κ : Clock)(α : Tick κ)(ρ : Γ c κ) → A κ ρ → A α (next c κ α ρ)
    Ty-next-ass : (κ : Clock)(α : Tick κ)(β : Tick α)
      → (ρ : Γ c κ)(x : A κ ρ)
      → Ty-next α β (next c κ α ρ) (Ty-next κ α ρ x) ≅ Ty-next κ β ρ x 
open Ty

-- Terms.

record ClTm ℓ (c : ClTy ℓ) : Set ℓ where
  constructor tm
  field
    τ : (κ : Clock) → Γ c κ
    Tm-next : (κ : Clock) (α : Tick κ) 
      → next c κ α (τ κ) ≅ τ α  -- : Γ c α

record Tm ℓ (c : Ctx ℓ)(t : Ty ℓ c) : Set ℓ where
  constructor tm
  field
    τ : (κ : Clock) (ρ : Γ c κ) → A t κ ρ
    Tm-next : (κ : Clock) (α : Tick κ) (ρ : Γ c κ)
      → Ty-next t κ α ρ (τ κ ρ) ≅ τ α (next c κ α ρ) -- : A t α (next c κ α ρ)

-- Empty context.

record ⊤ {ℓ} : Set ℓ where
  instance constructor tt

• : ∀ ℓ → Clock → Set ℓ
• ℓ _ = ⊤

•-next : ∀ {ℓ} → (κ : Clock) (α : Tick κ) → • ℓ κ → • ℓ α
•-next _ _ _ = tt

•-next-ass : ∀{ℓ} → (κ : Clock) (α : Tick κ) (β : Tick α) (ρ : • ℓ κ)
  → •-next α β (•-next κ α ρ) ≅ •-next κ β ρ
•-next-ass _ _ _ _ = refl

•-Ctx : ∀ ℓ → Ctx ℓ
•-Ctx ℓ = ctx (• ℓ) •-next •-next-ass

-- Contexts are types in the empty context.

ctx→ty : ∀ {ℓ} (c : Ctx ℓ)
  → (κ : Clock) → Γ (•-Ctx ℓ) κ → Set ℓ
ctx→ty (ctx Γ _ _) κ _ = Γ κ

ctx→ty-next : ∀ {ℓ} (c : Ctx ℓ)
  → (κ : Clock) (α : Tick κ) (ρ : Γ (•-Ctx ℓ) κ)
  → ctx→ty c κ ρ → ctx→ty c α (next (•-Ctx ℓ) κ α ρ)
ctx→ty-next (ctx Γ n _) κ α _ = n κ α

ctx→ty-next-ass : ∀ {ℓ} (c : Ctx ℓ)
  → (κ : Clock) (α : Tick κ) (β : Tick α) (ρ : Γ (•-Ctx ℓ) κ)
  → (x : ctx→ty c κ ρ)
  → ctx→ty-next c α β (next (•-Ctx ℓ) κ α ρ) (ctx→ty-next c κ α ρ x) ≅
    ctx→ty-next c κ β ρ x
ctx→ty-next-ass (ctx Γ n a) κ α β _ x = a κ α β x

Ctx→Ty : ∀ {ℓ} → Ctx ℓ → Ty ℓ (•-Ctx ℓ)
Ctx→Ty c = ty (ctx→ty c) (ctx→ty-next c) (ctx→ty-next-ass c)

Ctx→Tm : ∀ {ℓ} (c : Ctx ℓ)
  → {!!}
  → Tm ℓ (•-Ctx ℓ) (Ctx→Ty c)
Ctx→Tm c = {!!}

_⇒-fst_ : ∀ {ℓ ℓ'} (A : ClTy ℓ) (B : ClTy ℓ')
  → Clock → Set (ℓ' ⊔ ℓ) 
((ctx A nA aA) ⇒-fst (ctx B nB aB)) κ =
  Σ ((α : Tick κ) → A α → B α)
    (λ f → (α : Tick κ) (β : Tick α) (x : A α)
           → nB α β (f α x) ≅ f β (nA α β x)) 

_⇒_ : ∀ {ℓ ℓ'} → ClTy ℓ → ClTy ℓ' → ClTy (ℓ' ⊔ ℓ)
b ⇒ c = ctx (b ⇒-fst c) {!!} {!!}

{-
-- Pi types.

∏-fst : ∀ {ℓ ℓ'} (A : ClTy ℓ) (B : Ty ℓ' A)
  → Clock → Set (ℓ' ⊔ ℓ) 
∏-fst (ctx A nA aA) (ty B nB aB) κ =
  Σ ((α : Tick κ) (x : A α) → B α x)
    (λ f → (α : Tick κ) (β : Tick α) (x : A α)
           → nB α β x (f α x) ≅ f β (nA α β x)) -- : B β (nA α β x)

∏ : ∀ {ℓ ℓ'} (c : ClTy ℓ) (t : Ty ℓ' c) → ClTy (ℓ' ⊔ ℓ)
∏ c t = ctx (∏-fst c t) {!!} {!!}

_⇒_ : ∀ {ℓ ℓ'} → ClTy ℓ → ClTy ℓ' → ClTy (ℓ' ⊔ ℓ)
c ⇒ c' = ∏ c {!Ctx→Ty!}
-}

-- The later modality. The type ⊳ A κ looks like a dependent function
-- space, as in CloTT.

record ⊳-fst {ℓ} (A : Clock → Set ℓ) (κ : Clock) : Set ℓ where 
  coinductive
  constructor later
  field force : (α : Tick κ) → A α
open ⊳-fst

⊳ :  ∀{ℓ} → ClTy ℓ → ClTy ℓ
⊳ (ctx A n a) = ctx (⊳-fst A) {!!} {!!}

fix-fst : ∀{ℓ} (A : Clock → Set ℓ)
  → (κ : Clock) (α : Size< κ)
  → ((β : Clock) → β ≤ˢ α → ⊳-fst A β → A β) → A α
dfix-fst : ∀{ℓ} (A : Clock → Set ℓ)
  → (κ : Clock) (α : Size< κ)
  → ((β : Clock) → β ≤ˢ α → ⊳-fst A β → A β) → ⊳-fst A α
fix-fst A κ α f = f α refl≤ˢ (dfix-fst A κ α f)
force (dfix-fst A κ α f) β = fix-fst A α β f'
  where
    f' : (γ : Clock) → γ ≤ˢ β → ⊳-fst A γ → A γ
    f' .β refl≤ˢ x = f β (<-≤ˢ β) x
    f' .γ (<-≤ˢ γ) x = f γ (<-≤ˢ γ) x

fix : ∀{ℓ} (A : ClTy ℓ) → ClTm ℓ ((⊳ A ⇒ A) ⇒ A)
fix A = tm {!!} {!!}
  where
    fix'' : (κ : Clock) (α : Size< κ) → Γ (⊳ A ⇒ A) α → Γ A α
    fix'' κ α (f , p) = {!!}
  
    fix' : (κ : Clock) → Γ ((⊳ A ⇒ A) ⇒ A) κ
    fix' κ = fix'' κ , {!!}


{-

-- We have to postulate extensional equality for the later modality. I
-- am not completely sure this is correct... Should this be defined
-- only on ⊳ A ∞ ? That's how it is done in the literature (Abel
-- papers) for other coinductive types.

record _⊳[_]≡_ {ℓ}
               {A : Clock → Set ℓ}
               {κ : Clock}
               (x : ⊳ A κ)
               (κ' : Clock)
               (y : ⊳ A κ) : Set ℓ where 
  coinductive
  field force-eq : (α : Tick κ') → force x ≅ force y
open _⊳[_]≡_

postulate
  ⊳≡ : ∀ {ℓ} {A : Clock → Set ℓ} {κ : Clock} {x y : ⊳ A κ} → x ⊳[ ∞ ]≡ y → x ≅ y

 
-- Functoriality of ⊳. So ⊳ lifts to an operation on contexts.

⊳-next : ∀{ℓ} (A : Clock → Set ℓ) (κ : Clock) (α : Tick κ) → ⊳ A κ → ⊳ A α
force (⊳-next A κ α ρ) = force ρ

⊳-eq-next-ass : ∀{ℓ} (A : Clock → Set ℓ)
  → (κ : Clock) (α : Tick κ) (β : Tick α) {κ' : Clock} (a : ⊳ A κ)
  → ⊳-next A α β (⊳-next A κ α a) ⊳[ κ' ]≡ ⊳-next A κ β a
force-eq (⊳-eq-next-ass A κ α β a) γ = refl

⊳-next-ass : ∀{ℓ} (A : Clock → Set ℓ) (κ : Clock) (α : Tick κ) (β : Tick α)
  → (a : ⊳ A κ) → ⊳-next A α β (⊳-next A κ α a) ≅ ⊳-next A κ β a
⊳-next-ass A κ α β a = ⊳≡ (⊳-eq-next-ass A κ α β a)


⊳-Ctx :  ∀{ℓ} → Ctx ℓ → Ctx ℓ
⊳-Ctx (ctx Γ _ _) = ctx (⊳ Γ) (⊳-next Γ) (⊳-next-ass Γ) 


-- Pi types.

∏ : ∀ {ℓ ℓ'} (A : Clock → Set ℓ) (B : (κ : Clock) → A κ → Set ℓ')
  → Clock → Set (ℓ' ⊔ ℓ)
∏ A B κ = (α : Tick κ) → (x : A α) → B α x

∏-next : ∀ {ℓ ℓ'} (A : Clock → Set ℓ) (B : (κ : Clock) → A κ → Set ℓ')
  → (κ : Clock) (α : Tick κ) → ∏ A B κ → ∏ A B α
∏-next A B κ α f x = f x

∏-next-ass : ∀ {ℓ ℓ'} (A : Clock → Set ℓ) (B : (κ : Clock) → A κ → Set ℓ')
  → (κ : Clock) (α : Tick κ) (β : Tick α) (ρ : ∏ A B κ) 
  → ∏-next A B α β (∏-next A B κ α ρ) ≅ ∏-next A B κ β ρ
∏-next-ass A B κ α β ρ = refl

∏-Ty : ∀ {ℓ ℓ'} (c : ClTy ℓ) (t : Ty ℓ' c) → ClTy (ℓ' ⊔ ℓ)
∏-Ty (ctx Γ _ _) (ty A _ _) = ctx (∏ Γ A) (∏-next Γ A) (∏-next-ass Γ A)

-- Sigma types.

Σ≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
  → {a a' : A}{b : B a}{b' : B a'}
  → a ≅ a' → b ≅ b' → _≅_ {A = Σ A B} (a , b) {B = Σ A B} (a' , b')
Σ≡ refl refl = refl

∑ : ∀ {ℓ ℓ'} (A : Clock → Set ℓ) (B : (κ : Clock) → A κ → Set ℓ')
  → Clock → Set (ℓ' ⊔ ℓ)
∑ A B κ = Σ (A κ) (B κ)

_⊗_ : ∀ {ℓ ℓ'} (A : Clock → Set ℓ) (A : Clock → Set ℓ') → Clock → Set (ℓ' ⊔ ℓ)
A ⊗ B = ∑ A (λ κ _ → B κ)

∑-next : ∀ {ℓ ℓ'} (c : Ctx ℓ) (t : Ty ℓ' c)
  → (κ : Clock) (α : Tick κ) → ∑ (Γ c) (A t) κ → ∑ (Γ c) (A t) α
∑-next (ctx Γ nΓ _) (ty A nA _) κ α (ρ , x) = nΓ κ α ρ , nA κ α ρ x

∑-next-ass : ∀ {ℓ ℓ'} (c : Ctx ℓ) (t : Ty ℓ' c)
  → (κ : Clock) (α : Tick κ) (β : Tick α) (ρ : ∑ (Γ c) (A t) κ)
  → ∑-next c t α β (∑-next c t κ α ρ) ≅ ∑-next c t κ β ρ
∑-next-ass (ctx _ _ aΓ) (ty _ _ aA) κ α β (ρ , x) =
  Σ≡ (aΓ κ α β ρ) (aA κ α β ρ x)

∑-Ty : ∀ {ℓ ℓ'} (c : ClTy ℓ) (t : Ty ℓ' c) → ClTy (ℓ' ⊔ ℓ)
∑-Ty c t = ctx (∑ (Γ c) (A t)) (∑-next c t) (∑-next-ass c t)

-- Dependent later modality.

record ⊳-dep {ℓ ℓ'} {Γ : Clock → Set ℓ}
                    (A : (κ : Clock) → Γ κ → Set ℓ')
                    (κ : Clock) (ρ : ⊳ Γ κ) : Set ℓ' where
  coinductive
  constructor later-dep
  field force : (α : Tick κ) → A α (force ρ α)
open ⊳-dep

record _⊳-dep[_]≅_ {ℓ ℓ'} {Γ : Clock → Set ℓ}
                          {A : (κ : Clock) → Γ κ → Set ℓ'}
                          {κ : Clock}
                          {ρ ρ' : ⊳ Γ κ}
                          (x : ⊳-dep A κ ρ)
                          (κ' : Clock)
                          (y : ⊳-dep A κ ρ') : Set ℓ' where 
  coinductive
  field force-eq : (α : Tick κ') → force x ≅ force y
open _⊳-dep[_]≅_

postulate 
  ⊳-dep≡ : ∀ {ℓ ℓ'} {Γ : Clock → Set ℓ} {A : (κ : Clock) → Γ κ → Set ℓ'}
    → {κ : Clock} {ρ γ : ⊳ Γ κ} {x : ⊳-dep A κ ρ} {y : ⊳-dep A κ γ}
    → ρ ≅ γ → x ⊳-dep[ ∞ ]≅ y → x ≅ y

⊳-dep-next : ∀{ℓ ℓ'} {Γ : Clock → Set ℓ} (A : (κ : Clock) → Γ κ → Set ℓ')
  → (κ : Clock) (α : Tick κ) (ρ : ⊳ Γ κ)
  → ⊳-dep A κ ρ
  → ⊳-dep A α (⊳-next Γ κ α ρ)
force (⊳-dep-next A κ α ρ x) = force x

⊳-dep-eq-next-ass : ∀{ℓ ℓ'} {Γ : Clock → Set ℓ} (A : (κ : Clock) → Γ κ → Set ℓ')
  → (κ : Clock) (α : Tick κ) (β : Tick α) {κ' : Clock}
  → (ρ : ⊳ Γ κ) (x : ⊳-dep A κ ρ)
  → ⊳-dep-next A α β (⊳-next Γ κ α ρ) (⊳-dep-next A κ α ρ x) ⊳-dep[ κ' ]≅
    ⊳-dep-next A κ β ρ x
force-eq (⊳-dep-eq-next-ass A κ α β ρ x) _ = refl    

⊳-dep-next-ass : ∀{ℓ ℓ'} {Γ : Clock → Set ℓ} (A : (κ : Clock) → Γ κ → Set ℓ')
  → (κ : Clock) (α : Tick κ) (β : Tick α) (ρ : ⊳ Γ κ) (x : ⊳-dep A κ ρ)
  → ⊳-dep-next A α β (⊳-next Γ κ α ρ) (⊳-dep-next A κ α ρ x) ≅
    ⊳-dep-next A κ β ρ x
⊳-dep-next-ass A κ α β ρ x =
  ⊳-dep≡ (⊳-next-ass _ κ α β ρ) (⊳-dep-eq-next-ass A κ α β ρ x)

⊳-Ty :  ∀{ℓ ℓ'}(c : Ctx ℓ) → Ty ℓ' c → Ty ℓ' (⊳-Ctx c)
⊳-Ty (ctx Γ _ _) (ty A _ _) = ty (⊳-dep A) (⊳-dep-next A) (⊳-dep-next-ass A)

-- ⊳ is an applicative functor.

app : ∀ {ℓ ℓ'} {Γ : Clock → Set ℓ} {A : (κ : Clock) → Γ κ → Set ℓ'}
  → (κ : Clock) → ⊳ (∏ Γ A) κ → ∏ (⊳ Γ) (⊳-dep A) κ
force (app κ f α x) β = force f α β (force x β)

-- Clock quantification

& : ∀ {ℓ} → (Clock → Set ℓ) → Set ℓ
& A = (κ : Clock) → A κ

const : ∀ {ℓ} → Set ℓ → (Clock → Set ℓ)
const A _ = A

□ : ∀ {ℓ} → (Clock → Set ℓ) → (Clock → Set ℓ)
□ A = const (& A)


-- Fixpoints.

fix : ∀ {ℓ} {A : Clock → Set ℓ}
  → ((κ : Clock) → ⊳ A κ → A κ)
  → (κ : Clock) → A κ
dfix : ∀ {ℓ} {A : Clock → Set ℓ}
  → ((κ : Clock) → ⊳ A κ → A κ)
  → (κ : Clock) → ⊳ A κ
fix f κ = f κ (dfix f κ)
force (dfix f κ) α = fix f α

fix' : ∀ {ℓ} {A : Clock → Set ℓ}
  → ((κ : Clock) (α : Tick κ) → ⊳ A α → A α)
  → (κ : Clock) → A κ
dfix' : ∀ {ℓ} {A : Clock → Set ℓ}
  → ((κ : Clock) (α : Tick κ) → ⊳ A α → A α)
  → (κ : Clock) → ⊳ A κ
fix' f κ = f ∞ κ (dfix' f κ)
force (dfix' f κ) α = fix' f α

-- Universe

U : ∀ ℓ → Clock → Set (lsuc ℓ)
U ℓ _ = Set ℓ

--El : ∀ {ℓ} → (κ : Clock) → Set ℓ → U ℓ κ
--El _ X = X

--⊳U : ∀ {ℓ} → (κ : Clock) → ⊳ (U ℓ) κ → U ℓ κ
--⊳U = ⊳-dep (λ _ X → X)

--⊳U : ∀ {ℓ} → ((κ : Clock) (α : Tick κ) → U ℓ α) → (κ : Clock) → U ℓ κ
--⊳U X κ = ⊳-dep (λ _ B → B) κ (later (X κ))

-- Streams.

gStr : ∀ ℓ → Clock → Set ℓ
gStr ℓ = fix (λ κ X → ℕ × ⊳-dep (λ _ B → B) κ X)

{-
gStr' : ∀ ℓ → Clock → Set ℓ
gStr' ℓ = fix' F
  where
    F : (κ : Clock) (α : Tick κ) → ⊳ (λ _ → Set ℓ) α → Set ℓ
    F κ α X = ℕ × ⊳U {!!} {!!}
--fix (λ κ X → ℕ × ⊳U κ X)
-}

gStr-next : ∀ {ℓ} (κ : Clock) (α : Tick κ) → gStr ℓ κ → gStr ℓ α
gStr-next κ α (n , s) = n ,
  subst (⊳-dep (λ _ B → B) α)
        (⊳≡ (record { force-eq = λ _ → refl }))
        (⊳-dep-next (λ _ B → B) κ α (dfix (λ κ' X → ℕ × ⊳-dep (λ _ B → B) κ' X) κ) s)

{-
gStr-next-ass : ∀ {ℓ} (κ : Clock) (α : Tick κ) (β : Tick α) (ρ : gStr ℓ κ)
  → gStr-next α β (gStr-next κ α ρ) ≅ gStr-next κ β ρ
gStr-next-ass {ℓ} κ α β (n , s) = cong (_,_ n)
  (trans (subst-removable (⊳-dep (λ _ B → B) β)
                          (⊳≡ (record { force-eq = λ _ → refl }))
                          (⊳-dep-next (λ _ B → B) α β
                                      (dfix (λ κ' X → ℕ × ⊳-dep (λ _ B → B) κ' X) α)
                                      (proj₂ (gStr-next κ α (n , s)))))
         (trans (trans (⊳-dep≡ (trans (⊳≡ (record { force-eq = λ _ → refl })) (sym (⊳-next-ass (λ _ → Set ℓ) κ α β (dfix (λ κ' X → ℕ × ⊳-dep (λ _ B → B) κ' X) κ))))
                               {!!})
                       (⊳-dep-next-ass (λ _ B → B) κ α β (dfix (λ κ' X → ℕ × ⊳-dep (λ _ B → B) κ' X) κ) s))
                (sym (subst-removable (⊳-dep (λ _ B → B) β)
                                      (⊳≡ (record { force-eq = λ _ → refl }))
                                      (⊳-dep-next (λ _ B → B) κ β
                                                  (dfix (λ κ' X → ℕ × ⊳-dep (λ _ B → B) κ' X) κ)
                                                  s)))))

-}

gStr-ClTy : ∀ ℓ → Ctx ℓ
gStr-ClTy ℓ = ctx (gStr ℓ) gStr-next {!!}

ghd : ∀ {ℓ} (κ : Clock) → gStr ℓ κ → ℕ 
ghd κ s = proj₁ s

gtl : ∀ {ℓ} (κ : Clock) → gStr ℓ κ → ⊳ (gStr ℓ) κ 
force (gtl κ s) = force (proj₂ s)

gcons : ∀ {ℓ} (κ : Clock) → ℕ → ⊳ (gStr ℓ) κ → gStr ℓ κ
gcons κ n s = n , later-dep (force s)

ghd-gcons : ∀ {ℓ} (κ : Clock) (n : ℕ) (s : ⊳ (gStr ℓ) κ)
  → ghd κ (gcons κ n s) ≅ n
ghd-gcons κ n s = refl

eq-gtl-gcons : ∀ {ℓ} (κ : Clock) (n : ℕ) (s : ⊳ (gStr ℓ) κ) {κ' : Clock}
  → gtl κ (gcons κ n s) ⊳[ κ' ]≡ s
force-eq (eq-gtl-gcons κ n s) _ = refl 

gtl-gcons : ∀ {ℓ} (κ : Clock) (n : ℕ) (s : ⊳ (gStr ℓ) κ)
  → gtl κ (gcons κ n s) ≅ s
gtl-gcons κ n s = ⊳≡ (eq-gtl-gcons κ n s)

eq-gcons-ghd-gtl : ∀ {ℓ} (κ : Clock) (s : gStr ℓ κ) {κ' : Clock}
  → proj₂ (gcons κ (ghd κ s) (gtl κ s)) ⊳-dep[ κ' ]≅ proj₂ s
force-eq (eq-gcons-ghd-gtl κ (n , s)) _ = refl  

gcons-ghd-gtl : ∀ {ℓ} (κ : Clock) (s : gStr ℓ κ)
  → gcons κ (ghd κ s) (gtl κ s) ≅ s
gcons-ghd-gtl κ (n , s) =
  cong (_,_ n) (⊳-dep≡ refl (eq-gcons-ghd-gtl κ (n , s)))


κ₀ : Clock
κ₀ = ∞

_[◇] : ∀ {ℓ} {A : Clock → Set ℓ}
  → (t : (κ : Clock) → ⊳ A κ)
  → (κ : Clock) → A κ
(t [◇]) = force (t ∞)


Str : ∀ ℓ → Clock → Set ℓ
Str ℓ = □ (gStr ℓ)


--Str-Ty : ∀ {ℓ} → Ty ℓ {!!}
--Str-Ty = {!!}

hd : ∀ {ℓ} → & (gStr ℓ) → ℕ 
hd s = ghd κ₀ (s κ₀)

tl : ∀ {ℓ} → & (gStr ℓ) → & (gStr ℓ)
tl s = (λ κ → gtl κ (s κ)) [◇]

cons : ∀ {ℓ} → ℕ → & (gStr ℓ) → & (gStr ℓ)
cons n s κ = gcons κ n (later s)

hd-cons : ∀ {ℓ} (n : ℕ) (s : & (gStr ℓ))
  → hd (cons n s) ≅ n
hd-cons n s = refl

tl-cons : ∀ {ℓ} (n : ℕ) (s : & (gStr ℓ))
  → tl (cons n s) ≅ s
tl-cons n s = refl

postulate
  funext : ∀{ℓ ℓ'} {A : Set ℓ}{B : A → Set ℓ'}
    → {f g : (x : A) → B x}
    → ((x : A) → f x ≅ g x)
    → f ≅ g


cons-hd-tl : ∀ {ℓ} (s : & (gStr ℓ))
  → cons (hd s) (tl s) ≅ s
cons-hd-tl s = funext (λ κ → {!!}) --cong₂ _,_ {!!} (⊳-dep≡ refl (record { force-eq = {!!} })))

-}
