{-# OPTIONS --rewriting #-}

module Correctness where

open import Data.List 
open import Data.List.Relation.Unary.All hiding (map)
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.Maybe hiding (map)
open import Data.Sum hiding (map; swap)
open import Data.Product hiding (map; swap)
open import Data.Unit
open import Data.Empty
open import Data.Bool renaming (Bool to Tag; true to ∙; false to ∘)
open import Relation.Binary.PropositionalEquality hiding (_≗_)

open import Utilities
open import Formulae
open import SeqCalc

open import MultifocSeqCalc
--import MaxMultifocSeqCalc as MMF

infixl 15 _•_

data _≗⇑_ : {S : Stp}{Γ : Cxt}{A : Fma} (f g : S ∣ Γ ⇑ A) → Set
data _≗⇓_ : {b c : Tag} {S : Stp}{Γ : Cxt}{A : Fma} (f g : [ b , c ] S ∣ Γ ⇓ A) → Set
data _≗lf_ {Q : Fma}{q : isPosAt Q} : {S : Stp}{Γ : Cxt} (f g : q ⇛lf S ； Γ) → Set
data _≗rf_ : {s : Maybe (Σ Fma isNegAt)}{Γ : Cxt}{C : Fma} (f g : s ⇛rf Γ ； C) → Set
data _≗s⇑_ : ∀ {Ξ} (fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ) → Set 

data _≗⇑_ where

-- -- equivalence relation
  refl : ∀{S Γ A} {f : S ∣ Γ ⇑ A} → f ≗⇑ f
  ~_ : ∀{S Γ A} {f g : S ∣ Γ ⇑ A} → f ≗⇑ g → g ≗⇑ f
  _•_ : ∀{S Γ A} {f g h : S ∣ Γ ⇑ A} → f ≗⇑ g → g ≗⇑ h → f ≗⇑ h

-- -- congruence
  ⊸r : ∀{S Γ A C} {f g : S ∣ Γ ∷ʳ A ⇑ C} → f ≗⇑ g → ⊸r f ≗⇑ ⊸r g
  Il : ∀{Γ Q q q'} {f g : ─ ∣ Γ ⇑ Q} → f ≗⇑ g → Il q f ≗⇑ Il q' g
  ⊗l : ∀{Γ A B Q q q'} {f g : just A ∣ B ∷ Γ ⇑ Q} → f ≗⇑ g → ⊗l q f ≗⇑ ⊗l q' g
  foc : ∀{S Γ Q s s' q q'} {f g : [ ∘ , ∘ ] S ∣ Γ ⇓ Q} (eq : f ≗⇓ g) → foc s q f ≗⇑ foc s' q' g

-- -- multifocusing


data _≗⇓_ where

  refl : ∀{b c S Γ A} {f : [ b , c ] S ∣ Γ ⇓ A} → f ≗⇓ f
  ~_ : ∀{b c S Γ A} {f g : [ b , c ] S ∣ Γ ⇓ A} → f ≗⇓ g → g ≗⇓ f
  _•_ : ∀{b c S Γ A} {f g h : [ b , c ] S ∣ Γ ⇓ A} → f ≗⇓ g → g ≗⇓ h → f ≗⇓ h

  focl : ∀ {b S Γ Γ₀ Γ₁ C Q q}
         {h k : q ⇛lf S ； Γ₀} → 
         h ≗lf k → 
         {f g : [ ∙ , b ] just Q ∣ Γ₁ ⇓ C}
         {eq eq' : Γ ≡ Γ₀ ++ Γ₁} →
         f ≗⇓ g →
         focl _ h f eq ≗⇓ focl _ k g eq'

  focr : ∀ {b S Γ Γ₀ Γ₁ C M m}
         {h k : just (M , m) ⇛rf Γ₁ ； C} →
         h ≗rf k → 
         {f g : [ b , ∙ ] S ∣ Γ₀ ⇓ M} → 
         {eq eq' : Γ ≡ Γ₀ ++ Γ₁} → 
         f ≗⇓ g →
         focr _ h f eq ≗⇓ focr _ k g eq'

  focrn : ∀ {b S Γ Γ₀ Γ₁ C}
         {h k : nothing ⇛rf Γ₁ ； C} →
         h ≗rf k →
         {f g : S ≡ nothing × Γ₀ ≡ []}
         {eq eq' : Γ ≡ Γ₀ ++ Γ₁} → 
         focr {b} nothing h f eq ≗⇓ focr nothing k g eq'

  unfoc : ∀ {b c S Γ C}
          {ok : UT b c S C}
          {f g : S ∣ Γ ⇑ C} →
          (eq : f ≗⇑ g) → 
          unfoc {b}{c} ok f ≗⇓ unfoc ok g

  swap : ∀ {S Γ₀ Γ₁ Γ₂ C M Q q m}
         {lf : q ⇛lf S ； Γ₀} {rf : just (M , m) ⇛rf Γ₂ ； C}
         {f : [ ∙ , ∙ ] just Q ∣ Γ₁ ⇓ M} →
         focl q lf (focr _ rf f refl) refl ≗⇓ focr _ rf (focl q lf f refl) refl

  early-lf : ∀ {S Γ Γ₀ Γ₁} Δ {Q R} {s : isIrr S} {n : isNeg (Δ ⊸⋆ R)} {q : isPos Q} (r : isPosAt R)
            {lf : pos→posat q ⇛lf S ； Γ₀} 
            {f : just Q ∣ Γ₁ ++ Δ ⇑ R} {eq : Γ ≡ Γ₀ ++ Γ₁} {eq' : Γ ++ Δ ≡ Γ₀ ++ Γ₁ ++ Δ} →
            unfoc {∘}{∙} n (⊸r⋆⇑ Δ (foc s r (focl {∘} (pos→posat q) lf (unfoc {∙}{∘} q f) eq')))
              ≗⇓ focl {∙} _ lf (unfoc {∙}{∙} (inj₁ q) (⊸r⋆⇑ Δ f)) eq

  early-lf-at : ∀ {S Γ Γ₀ Γ₁} Δ {X R} {s : isIrr S} {n : isNeg (Δ ⊸⋆ R)} {x : isAt X} (r : isPosAt R)
              {lf : at→posat x ⇛lf S ； Γ₀} 
              {f : [ ∙ , ∘ ] just X ∣ Γ₁ ++ Δ ⇓ R} {eq : Γ ≡ Γ₀ ++ Γ₁} {eq' : Γ ++ Δ ≡ Γ₀ ++ Γ₁ ++ Δ} →
              unfoc {∘}{∙} n (⊸r⋆⇑ Δ (foc s r (focl {∘} (at→posat x) lf f eq')))
                ≗⇓ focl {∙} _ lf (unfoc {∙}{∙} (inj₂ n) (⊸r⋆⇑ Δ (foc (at→negat x) r (focl (at→posat x) blurl f refl)))) eq

  early-rf : ∀ {T Γ Γ₁ Γ₂ Δ N Q R} t {n} {q : isPos Q} {r}
            {rf : just (N , neg→negat n) ⇛rf Γ₂ ； R}
            {f : T ∣ Δ ++ Γ₁ ⇑ N} (ℓ : L T Δ Q) {eq : Γ ≡ Γ₁ ++ Γ₂} →
            unfoc {∙}{∘} q (runL {Δ = Γ} ℓ (foc t r (focr {∘} {Γ₀ = Δ ++ Γ₁}{Γ₂}_ rf (unfoc {∘}{∙} n f) (cong (Δ ++_) eq))))
              ≗⇓ focr {∙} _ rf (unfoc {∙}{∙} (inj₁ q) (runL {Δ = Γ₁} ℓ f)) eq

  early-rf-at : ∀ {T Γ Γ₁ Γ₂ Δ X Q R} t {x} {q : isPos Q} {r}
                {rf : just (X , at→negat x) ⇛rf Γ₂ ； R}
                {f : [ ∘ , ∙ ] T ∣ Δ ++ Γ₁ ⇓ X} (ℓ : L T Δ Q) {eq : Γ ≡ Γ₁ ++ Γ₂} →
              unfoc {∙}{∘} q (runL {Δ = Γ} ℓ (foc t r (focr {∘} {Γ₀ = Δ ++ Γ₁}{Γ₂} _ rf f (cong (Δ ++_) eq))))
              ≗⇓ focr {∙} _ rf (unfoc {∙}{∙} (inj₁ q) (runL {Δ = Γ₁} ℓ (foc t (at→posat x) (focr (just (X , at→negat x)) blurr f refl)))) eq


  blurr-at : ∀ {Γ P X p} {f : just P ∣ Γ ⇑ ` X} → focr {∙} _ blurr (unfoc (inj₁ p) f) refl ≗⇓ unfoc {∙}{∘} p f
  blurl-at : ∀ {Γ N X n} {f : just (` X) ∣ Γ ⇑ N} → focl {∙} _ blurl (unfoc (inj₂ n) f) refl ≗⇓ unfoc {∘}{∙} n f

--   early-lf : ∀ {S Γ₀ Γ₁ Γ₂} Δ {C Q R s n q} r
--             {lf : pos→posat q ⇛lf S ； Γ₀} {rf : just (Δ ⊸⋆ R , neg→negat n) ⇛rf Γ₂ ； C}
--             {f : just Q ∣ Γ₁ ++ Δ ⇑ R} →
--             focr {∘} {Γ₀ = Γ₀ ++ Γ₁} _ rf (unfoc n (⊸r⋆⇑ Δ (foc s r (focl (pos→posat q) lf (unfoc q f) refl)))) refl
--               ≗⇓ focl _ lf (focr _ rf (unfoc (inj₁ q) (⊸r⋆⇑ Δ f)) refl) refl

--   early-rf : ∀ {S T Γ₀ Γ₁ Γ₂ Δ N Q R} t {n q r}
--             {lf : pos→posat q ⇛lf S ； Γ₀} {rf : just (N , neg→negat n) ⇛rf Γ₂ ； R}
--             {f : T ∣ Δ ++ Γ₁ ⇑ N} (ℓ : L T Δ Q) →
--             focl {∘} {Γ₀ = Γ₀} {Γ₁ ++ Γ₂} _ lf (unfoc q (runL {Δ = Γ₁ ++ Γ₂} ℓ (foc t r (focr {Γ₀ = Δ ++ Γ₁}{Γ₂}_ rf (unfoc n f) refl)))) refl
--               ≗⇓ focl _ lf (focr _ rf (unfoc (inj₁ q) (runL {Δ = Γ₁} ℓ f)) refl) refl

data _≗lf_ {Q}{q'} where

  refl : ∀ {S Γ} {f : q' ⇛lf S ； Γ} → f ≗lf f
  ~_ : ∀ {S Γ} {f g : q' ⇛lf S ； Γ} → f ≗lf g → g ≗lf f
  _•_ : ∀ {S Γ} {f g h : q' ⇛lf S ； Γ} → f ≗lf g → g ≗lf h → f ≗lf h

  pass : ∀ {Γ A} {f g : q' ⇛lf just A ； Γ} → f ≗lf g → pass f ≗lf pass g

  ⊸l+ : ∀ {Γ₀ Δ Γ' A₀ Q Ξ q}
           {fs gs : All (λ ΓA → ─ ∣ proj₁ ΓA ⇑ proj₂ ΓA) ((Γ₀ , A₀) ∷ Ξ)} → fs ≗s⇑ gs → 
           {f g : q' ⇛lf just Q ； Δ} → f ≗lf g → 
           {eq eq' : Γ' ≡ Γ₀ ++ concat (cxts Ξ) ++ Δ} → 
      ----------------------------------------------------------
          ⊸l+ Γ₀ Ξ q fs f eq ≗lf ⊸l+ Γ₀ Ξ q gs g eq'

data _≗rf_ where

  refl : ∀ {s Γ C} {f : s ⇛rf Γ ； C} → f ≗rf f
  ~_ : ∀ {s Γ C} {f g : s ⇛rf Γ ； C} → f ≗rf g → g ≗rf f
  _•_ : ∀ {s Γ C} {f g h : s ⇛rf Γ ； C} → f ≗rf g → g ≗rf h → f ≗rf h

  ⊗r+ : ∀ {Γ Γ' Δ₀ M B₀ s Ξ m}
        {f g : s ⇛rf Γ ； M} → f ≗rf g → 
        {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → fs ≗s⇑ gs → 
        {eq eq' : Γ' ≡ Γ ++ Δ₀ ++ concat (cxts Ξ)} →
      ------------------------------------
         ⊗r+ Δ₀ Ξ m f fs eq ≗rf ⊗r+ Δ₀ Ξ m g gs eq' 

data _≗s⇑_ where
  [] : [] ≗s⇑ []
  _∷_ : ∀ {Δ B Ξ} {f g : ─ ∣ Δ ⇑ B} (eq : f ≗⇑ g)
          {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ} (eqs : fs ≗s⇑ gs) →
          (f ∷ fs) ≗s⇑ (g ∷ gs) 

refl⇑ : ∀{S Γ A} {f g : S ∣ Γ ⇑ A} → f ≡ g → f ≗⇑ g
refl⇑ refl = refl

foc-same : ∀{S Γ Q s q} {f g : [ ∘ , ∘ ] S ∣ Γ ⇓ Q} (eq : f ≗⇓ g) → foc s q f ≗⇑ foc s q g
foc-same eq = foc eq



Il⇑eq : {Γ : Cxt} {Q : Fma} {q : isPosAt Q}
        (f :  ─ ∣ Γ ⇑ Q) →
  -------------------------
       Il⇑ f ≡ Il q f
Il⇑eq {Q = ` x} (foc s q f) = refl
Il⇑eq {Q = I} (foc s q f) = refl
Il⇑eq {Q = Q ⊗ Q₁} (foc s q f) = refl

⊗l⇑eq : {Γ : Cxt} {A B Q : Fma} {q : isPosAt Q}
        (f :  just A ∣ B ∷ Γ ⇑ Q) →
  -------------------------
       ⊗l⇑ f ≡ ⊗l q f
⊗l⇑eq {Q = ` x} (Il q f) = refl
⊗l⇑eq {Q = ` x} (⊗l q f) = refl
⊗l⇑eq {Q = ` x} (foc s q f) = refl
⊗l⇑eq {Q = I} (Il q f) = refl
⊗l⇑eq {Q = I} (⊗l q f) = refl
⊗l⇑eq {Q = I} (foc s q f) = refl
⊗l⇑eq {Q = Q ⊗ Q₁} (Il q f) = refl
⊗l⇑eq {Q = Q ⊗ Q₁} (⊗l q f) = refl
⊗l⇑eq {Q = Q ⊗ Q₁} (foc s q f) = refl

⊗r+Il⇑N : {Γ₀ Γ : Cxt} (Γ₁ Δ₀ : Cxt) {A B₀ : Fma}
           (n : isNeg (Γ₁ ⊸⋆ A))
           (Ξ : List (Cxt × Fma))
           (f : ─ ∣ Γ ⇑ A)
           (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ))
           (eq : Γ ≡ Γ₀ ++ Γ₁) →
           ⊗r+⇑N Γ₁ Δ₀ n Ξ (Il⇑ f) gs eq ≡ Il⇑ (⊗r+⇑N Γ₁ Δ₀ n Ξ f gs eq)
⊗r+Il⇑N Γ₁ Δ₀ n Ξ (⊸r f) gs refl = ⊗r+Il⇑N (Γ₁ ∷ʳ _) Δ₀ n Ξ f gs refl
⊗r+Il⇑N Γ₁ Δ₀ n Ξ (foc s q f) gs refl = refl

⊗r+Il⇑ : {Γ : Cxt} (Δ₀ : Cxt) {B₀ A : Fma}
          (Ξ : List (Cxt × Fma))
          (f : ─ ∣ Γ ⇑ A)
          (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)) →
    ---------------------------------------------------------------------
        ⊗r+⇑ Δ₀ Ξ (Il⇑ f) gs ≡ Il⇑ (⊗r+⇑ Δ₀ Ξ f gs)
⊗r+Il⇑ Δ₀ {A = ` X} Ξ (foc s q f) gs = refl
⊗r+Il⇑ Δ₀ {A = I} Ξ (foc s q f) gs = refl
⊗r+Il⇑ Δ₀ {A = A' ⊗ B'} Ξ (foc s q f) gs = refl
⊗r+Il⇑ Δ₀ {A = A' ⊸ B'} Ξ f gs = ⊗r+Il⇑N [] Δ₀ tt Ξ f gs refl

⊗r+⊗l⇑N : {Γ₀ Γ : Cxt} (Γ₁ Δ₀ : Cxt) {A' B' A B₀ : Fma}
           (n : isNeg (Γ₁ ⊸⋆ A))
           (Ξ : List (Cxt × Fma))
           (f : just A' ∣ B' ∷ Γ ⇑ A)
           (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ))
           (eq : Γ ≡ Γ₀ ++ Γ₁) →
           ⊗r+⇑N Γ₁ Δ₀ n Ξ (⊗l⇑ f) gs eq ≡ ⊗l⇑ (⊗r+⇑N Γ₁ Δ₀ n Ξ f gs (cong (B' ∷_) eq))
⊗r+⊗l⇑N Γ₁ Δ₀ n Ξ (⊸r f) gs refl = ⊗r+⊗l⇑N (Γ₁ ∷ʳ _) Δ₀ n Ξ f gs refl
⊗r+⊗l⇑N Γ₁ Δ₀ n Ξ (Il q f) gs refl = refl
⊗r+⊗l⇑N Γ₁ Δ₀ n Ξ (⊗l q f) gs refl =  refl
⊗r+⊗l⇑N Γ₁ Δ₀ {` X} n Ξ (foc s q f) gs refl = refl
⊗r+⊗l⇑N Γ₁ Δ₀ {_ ⊸ _} n Ξ (foc s q f) gs refl = refl

⊗r+⊗l⇑ : {Γ : Cxt} (Δ₀ : Cxt) {A' B' B₀ A : Fma}
          (Ξ : List (Cxt × Fma))
          (f : just A' ∣ B' ∷ Γ ⇑ A)
          (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)) →
    ---------------------------------------------------------------------
        ⊗r+⇑ Δ₀ Ξ (⊗l⇑ f) gs ≡ ⊗l⇑ (⊗r+⇑ Δ₀ Ξ f gs)
⊗r+⊗l⇑ Δ₀ {A = ` X} Ξ (Il q f) gs = refl
⊗r+⊗l⇑ Δ₀ {A = ` X} Ξ (⊗l q f) gs = refl
⊗r+⊗l⇑ Δ₀ {A = ` X} Ξ (foc s q f) gs = refl
⊗r+⊗l⇑ Δ₀ {A = I} Ξ (Il q f) gs = refl
⊗r+⊗l⇑ Δ₀ {A = I} Ξ (⊗l q f) gs = refl
⊗r+⊗l⇑ Δ₀ {A = I} Ξ (foc s q f) gs = refl
⊗r+⊗l⇑ Δ₀ {A = A' ⊗ B'} Ξ (Il q f) gs = refl
⊗r+⊗l⇑ Δ₀ {A = A' ⊗ B'} Ξ (⊗l q f) gs = refl
⊗r+⊗l⇑ Δ₀ {A = A' ⊗ B'} Ξ (foc s q f) gs = refl
⊗r+⊗l⇑ Δ₀ {A = A' ⊸ B'} Ξ f gs = ⊗r+⊗l⇑N [] Δ₀ tt Ξ f gs refl

⊸r⊸l⇑ : {Γ Δ : Cxt} {A B C D : Fma}
         (f : ─ ∣ Γ ⇑ A) (g : just B ∣ Δ ∷ʳ D ⇑ C) → 
    -----------------------------------------------------------------------
        ⊸r (⊸l⇑ f g) ≡ ⊸l⇑ f (⊸r g)
⊸r⊸l⇑ {B = ` X} f g = refl
⊸r⊸l⇑ {B = I} f g = refl
⊸r⊸l⇑ {B = B ⊗ B₁} f g = refl
⊸r⊸l⇑ {B = B ⊸ B₁} f g = refl

⊸r⋆⊸r⋆⇑ : {S : Stp} {Γ : Cxt} (Δ : Cxt) {Δ' : Cxt} {A : Fma}
         {f : S ∣ Γ ++ Δ ++ Δ' ⇑ A} →
         ⊸r⋆⇑ (Δ ++ Δ') f ≡ ⊸r⋆⇑ Δ (⊸r⋆⇑ {Γ = Γ ++ Δ} Δ' f)
⊸r⋆⊸r⋆⇑ [] = refl
⊸r⋆⊸r⋆⇑ (_ ∷ Δ) {Δ'} = cong ⊸r (⊸r⋆⊸r⋆⇑ Δ {Δ'})

⊸r⋆Il⇑ : {Γ : Cxt} (Δ : Cxt) {A : Fma}
         {f : ─ ∣ Γ ++ Δ ⇑ A} →
         ⊸r⋆⇑ Δ (Il⇑ f) ≡ Il⇑ (⊸r⋆⇑ Δ f)
⊸r⋆Il⇑ [] = refl
⊸r⋆Il⇑ (_ ∷ Δ) = cong ⊸r (⊸r⋆Il⇑ Δ)

⊸r⋆⊗l⇑ : {Γ : Cxt} (Δ : Cxt) {A A' B' : Fma}
         {f : just A' ∣ B' ∷ Γ ++ Δ ⇑ A} →
         ⊸r⋆⇑ Δ (⊗l⇑ f) ≡ ⊗l⇑ (⊸r⋆⇑ Δ f)
⊸r⋆⊗l⇑ [] = refl
⊸r⋆⊗l⇑ (_ ∷ Δ) = cong ⊸r (⊸r⋆⊗l⇑ Δ)

congIl⇑ : ∀{Γ C} {f g : ─ ∣ Γ ⇑ C} → f ≗⇑ g → Il⇑ f ≗⇑ Il⇑ g
congIl⇑ refl = refl
congIl⇑ (~ eq) = ~ congIl⇑ eq
congIl⇑ (eq • eq₁) = congIl⇑ eq • congIl⇑ eq₁
congIl⇑ (⊸r eq) = ⊸r (congIl⇑ eq)
congIl⇑ (foc eq) = Il (foc eq)

cong⊗l⇑ : ∀{Γ A B C} {f g : just A ∣ B ∷ Γ ⇑ C} → f ≗⇑ g → ⊗l⇑ f ≗⇑ ⊗l⇑ g
cong⊗l⇑ refl = refl
cong⊗l⇑ (~ eq) = ~ cong⊗l⇑ eq
cong⊗l⇑ (eq • eq₁) = cong⊗l⇑ eq • cong⊗l⇑ eq₁
cong⊗l⇑ (⊸r eq) = ⊸r (cong⊗l⇑ eq)
cong⊗l⇑ (Il eq) = ⊗l (Il eq)
cong⊗l⇑ (⊗l eq) = ⊗l (⊗l eq)
cong⊗l⇑ (foc eq) = ⊗l (foc eq) 

cong⊸r⋆⇑ : {S : Stp} {Γ : Cxt} (Δ : Cxt) {A : Fma}
           {f g : S ∣ Γ ++ Δ ⇑ A} → f ≗⇑ g → 
           ⊸r⋆⇑ Δ f ≗⇑ ⊸r⋆⇑ Δ g
cong⊸r⋆⇑ [] eq = eq
cong⊸r⋆⇑ (_ ∷ Δ) eq = ⊸r (cong⊸r⋆⇑ Δ eq)

congrunL : ∀{S Γ Δ A C} {f g : S ∣ Γ ++ Δ ⇑ C} (ℓ : L S Γ A)→ f ≗⇑ g
  → runL {Δ = Δ} ℓ f ≗⇑ runL ℓ g
congrunL done eq = eq
congrunL (Il-1 ℓ) eq = congrunL ℓ (congIl⇑ eq)
congrunL (⊗l-1 ℓ) eq = congrunL ℓ (cong⊗l⇑ eq)

swap' : ∀ {S Γ Γ₀ Γ₁ Γ₂ C M Q q m}
         {lf : q ⇛lf S ； Γ₀} {rf : just (M , m) ⇛rf Γ₂ ； C}
         {f : [ ∙ , ∙ ] just Q ∣ Γ₁ ⇓ M}
         (eq : Γ ≡ Γ₀ ++ Γ₁) {eq' : Γ ++ Γ₂ ≡ Γ₀ ++ Γ₁ ++ Γ₂} →
         focl q lf (focr _ rf f refl) eq' ≗⇓ focr _ rf (focl q lf f eq) refl
swap' refl {refl} = swap

swap'' : ∀ {S Γ Γ₀ Γ₁ Γ₂ C M Q q m}
         {lf : q ⇛lf S ； Γ₀} {rf : just (M , m) ⇛rf Γ₂ ； C}
         {f : [ ∙ , ∙ ] just Q ∣ Γ₁ ⇓ M}
         (eq : Γ ≡ Γ₁ ++ Γ₂) {eq' : Γ₀ ++ Γ ≡ Γ₀ ++ Γ₁ ++ Γ₂} →
         focl q lf (focr _ rf f eq) refl ≗⇓ focr _ rf (focl q lf f refl) eq'
swap'' refl {refl} = swap

early-pass⇓-at : ∀ {Γ₀} Δ {X Q n q}
  → (x : isAt X)
  → (f : [ ∘ , ∘ ] just X ∣ Γ₀ ++ Δ ⇓ Q)
  → unfoc {∘}{∙} n (⊸r⋆⇑ Δ (foc tt q (pass⇓ f)))
          ≗⇓ focl (at→posat x) (pass blurl) (unfoc (inj₂ n) (⊸r⋆⇑ Δ (foc (at→negat x) q f))) refl

early-pass⇑-at : ∀ {Γ₀} Δ {X A n}
  → (x : isAt X)
  → (f : just X ∣ Γ₀ ++ Δ ⇑ A)
  → unfoc {∘}{∙} n (⊸r⋆⇑ Δ (pass⇑ f)) ≗⇓ focl (at→posat x) (pass blurl) (unfoc (inj₂ n) (⊸r⋆⇑ Δ f)) refl

early-pass⇑-at {Γ₀} Δ x (⊸r f) =
  unfoc (~ (refl⇑ (⊸r⋆⊸r⋆⇑ Δ {_ ∷ []})))
  • early-pass⇑-at {Γ₀} (Δ ∷ʳ _) x f
  • focl refl (unfoc (refl⇑ (⊸r⋆⊸r⋆⇑ Δ {_ ∷ []})))
early-pass⇑-at Δ {` X} x (foc s q f) = early-pass⇓-at Δ tt f

early-pass⇓-at Δ {` X} {q = q} x (focr (just (M , m)) rf (focl _ blurl f refl) eq) =
  unfoc (cong⊸r⋆⇑ Δ (foc-same (~ swap'' eq)))
  • early-lf-at Δ q {eq = refl}
  • focl refl (unfoc (cong⊸r⋆⇑ Δ (foc-same (swap'' eq))))
early-pass⇓-at Δ {` X} {q = q} x (focr (just (M , m)) rf (unfoc ok f) eq) = 
  unfoc (cong⊸r⋆⇑ Δ (foc-same (focr refl {eq' = cong (_ ∷_) eq} (early-pass⇑-at [] tt f) • ~ (swap'' eq))))
  • early-lf-at Δ q {eq = refl}
  • focl refl (unfoc (cong⊸r⋆⇑ Δ (foc-same (swap'' eq {eq} • focr refl blurl-at))))

early-pass⇓-at Δ {` X} {q = q} x (focl _ blurl f refl) = early-lf-at Δ q



{-
early-rf' : ∀ {T Γ₀ Γ₁ Γ₂ Γ} Γ' {Δ P Q Q' R} t {n : isNegAt (Γ' ⊸⋆ Q)} {p : isPos P} {q : isPosAt Q} {q' : isPos Q'} {r}
            {lf : pos→posat q' ⇛lf T ； Γ₀} {rf : just (Γ' ⊸⋆ Q , n) ⇛rf Γ₂ ； R}
            {f : just Q' ∣ Γ ++ Γ' ⇑ Q} (ℓ : L T Δ P) →
            (eq : Δ ++ Γ₁ ≡ Γ₀ ++ Γ) → 
            unfoc {∙}{∘} p (runL {Δ = Γ₁ ++ Γ₂} ℓ (foc t r (focr {∘} {Γ₀ = Δ ++ Γ₁}{Γ₂} _ rf (focl {Γ₀ = Γ₀}{Γ} _ lf (unfoc (inj₁ q') (⊸r⋆⇑ Γ' f)) eq) refl)))
              ≗⇓ focr {Γ₀ = Γ₁} {Γ₂} _ rf (unfoc (inj₁ p) (⊸r⋆⇑ Γ' (runL {Δ = Γ₁ ++ Γ'} ℓ (foc t q (focl {Γ₀ = Γ₀} {Γ ++ Γ'} _ lf (unfoc q' f) (cong (_++ Γ') {x = Δ ++ Γ₁}{Γ₀ ++ Γ} eq)))))) refl

early-rf' Γ' t {q = q} ℓ eq =
  unfoc (congrunL ℓ (foc-same (focr refl (~ (early-lf Γ' q)))))
  • {!!}

early-lf' : ∀ {S' S Γ₀ Γ₁ Γ₂ Γ Γ'} Δ {M Q R} {s : isIrr S} {s' : isIrr S'} {m : isNeg M} {n : isNeg (Δ ⊸⋆ R)} {q : isPos Q} (r : isPosAt R)
     {lf : pos→posat q ⇛lf S ； Γ₀} {rf : just (M , neg→negat m) ⇛rf Γ₂ ； R} 
     {f : S' ∣ Γ' ++ Γ ⇑ M} →  --Γ₁ ++ Δ
     (eq : Γ₁ ++ Δ ≡ Γ ++ Γ₂)
     (ℓ : L S' Γ' Q) → 
     _≗⇓_ {∘}{∙} {Γ = Γ₀ ++ Γ₁}
        (unfoc {∘}{∙} n (⊸r⋆⇑ Δ (foc s r (focl {∘}{Γ₀ = Γ₀}{Γ₁ ++ Δ} (pos→posat q) lf (focr {Γ₀ = Γ} {Γ₂} _ rf (unfoc (inj₁ q) (runL {Δ = Γ} ℓ f)) eq) refl))))
        (focl {∙} {Γ₀ = Γ₀}{Γ₁}  _ lf (unfoc {∙}{∙} (inj₁ q) (⊸r⋆⇑ Δ (runL {Δ = Γ₁ ++ Δ} ℓ (foc s' r (focr {Γ₀ = Γ' ++ Γ} _ rf (unfoc m f) (cong (Γ' ++_) eq)))))) refl)
early-lf' Δ r eq ℓ =
  unfoc (cong⊸r⋆⇑ Δ (foc-same (focl refl (~ (early-rf _ ℓ)))))
  • early-lf Δ r
-}


pass⊸r⋆⇑ : {Γ : Cxt} (Δ : Cxt) {A C : Fma}
           {f : just A ∣ Γ ++ Δ ⇑ C} →
  --------------------------------------------
        pass⇑ (⊸r⋆⇑ Δ f) ≡ ⊸r⋆⇑ Δ (pass⇑ f)
pass⊸r⋆⇑ [] = refl
pass⊸r⋆⇑ {Γ} (B ∷ Δ) = cong ⊸r (pass⊸r⋆⇑ {Γ ∷ʳ B} Δ)

congpass⇑ : ∀ {Γ A C} {f g : just A ∣ Γ ⇑ C} → f ≗⇑ g
  → pass⇑ f ≗⇑ pass⇑ g
congpass⇓ : ∀ {b Γ A C} {f g : [ ∘ , b ] just A ∣ Γ ⇓ C} → f ≗⇓ g
  → pass⇓ f ≗⇓ pass⇓ g

congpass⇑ refl = refl
congpass⇑ (~ eq) = ~ congpass⇑ eq
congpass⇑ (eq • eq₁) = congpass⇑ eq • congpass⇑ eq₁
congpass⇑ (⊸r eq) = ⊸r (congpass⇑ eq)
congpass⇑ (Il eq) = foc (focl refl (unfoc (Il eq)))
congpass⇑ (⊗l eq) = foc (focl refl (unfoc (⊗l eq)))
congpass⇑ (foc eq) = foc (congpass⇓ eq)

congpass⇓ refl = refl
congpass⇓ (~ eq) = ~ congpass⇓ eq
congpass⇓ (eq • eq₁) = congpass⇓ eq • congpass⇓ eq₁
congpass⇓ (focl eql eq) = focl (pass eql) eq
congpass⇓ (focr eqr eq) = focr eqr (congpass⇓ eq)
congpass⇓ {∙} (unfoc eq) = unfoc (congpass⇑ eq)
congpass⇓ swap = swap
congpass⇓ (early-lf Δ r {eq = refl}) = unfoc (refl⇑ (pass⊸r⋆⇑ Δ)) • early-lf Δ r
congpass⇓ (early-lf-at Δ r {eq = refl}) = unfoc (refl⇑ (pass⊸r⋆⇑ Δ)) • early-lf-at Δ r
congpass⇓ (blurl-at {f = f}) = ~ early-pass⇑-at [] tt f

Il⊗r+⇑Q : {Γ Δ₀ : Cxt} {B₀ Q : Fma}
          {q : isPosAt Q}
          {Ξ : List (Cxt × Fma)}
          (f : ─ ∣ Γ ⇑ Q)
          {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} →
          ⊗r+⇑Q Δ₀ q Ξ (Il⇑ f) gs ≡ Il⇑ (⊗r+⇑Q Δ₀ q Ξ f gs)
Il⊗r+⇑Q (foc s q f) = refl

⊗l⊗r+⇑Q : {Γ Δ₀ : Cxt} {A B B₀ Q : Fma}
          {q : isPosAt Q}
          {Ξ : List (Cxt × Fma)}
          (f : just A ∣ B ∷ Γ ⇑ Q)
          {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} →
          ⊗r+⇑Q Δ₀ q Ξ (⊗l⇑ f) gs ≡ ⊗l⇑ (⊗r+⇑Q Δ₀ q Ξ f gs)
⊗l⊗r+⇑Q (Il q f) = refl
⊗l⊗r+⇑Q (⊗l q f) = refl
⊗l⊗r+⇑Q (foc s q f) = refl

runL⊗r+⇑Q : {S : Stp} {Γ Δ Δ₀ : Cxt} {B₀ Q A : Fma}
            {q : isPosAt Q}
            {Ξ : List (Cxt × Fma)}
            {f : S ∣ Γ ++ Δ ⇑ Q}
            {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)}
            (ℓ : L S Γ A) → 
    ---------------------------------------------------------------------
        ⊗r+⇑Q Δ₀ q Ξ (runL {Δ = Δ} ℓ f) gs ≡
          runL {Δ = Δ ++ Δ₀ ++ concat (cxts Ξ)} ℓ (⊗r+⇑Q Δ₀ q Ξ f gs)

runL⊗r+⇑Q done = refl
runL⊗r+⇑Q (Il-1 ℓ) = trans (runL⊗r+⇑Q ℓ) (cong (runL ℓ) (Il⊗r+⇑Q _))
runL⊗r+⇑Q (⊗l-1 ℓ) = trans (runL⊗r+⇑Q ℓ) (cong (runL ℓ) (⊗l⊗r+⇑Q _))

cong⊗r+⇓Q₁ : ∀ {b S Γ Δ₀ B₀ Q q Ξ}
            {f f' : [ b , ∘ ] S ∣ Γ ⇓ Q} (eq : f ≗⇓ f') 
            {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} →  
    ---------------------------------------------------------------------
           ⊗r+⇓Q Δ₀ q Ξ f gs ≗⇓ ⊗r+⇓Q Δ₀ q Ξ f' gs

refls⇑ : ∀ {Ξ} {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ} → fs ≗s⇑ fs
refls⇑ {fs = []} = []
refls⇑ {fs = f ∷ fs} = refl ∷ refls⇑

++≗s₁ : ∀ {Ξ Ξ'} {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ}
  → fs ≗s⇑ gs
  → {hs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ'}
  → (fs ++All hs) ≗s⇑ (gs ++All hs)
++≗s₁ [] = refls⇑ 
++≗s₁ (eq ∷ eqs) = eq ∷ (++≗s₁ eqs)

++≗s₂ : ∀ {Ξ Ξ'} (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ)
  → {gs hs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ'}
  →  gs ≗s⇑ hs
  → (fs ++All gs) ≗s⇑ (fs ++All hs)
++≗s₂ [] eqs = eqs
++≗s₂ (f ∷ fs) eqs = refl ∷ (++≗s₂ fs eqs)

++rf≗₁ : ∀ {Δ₀ Γ B₀ C Ξ s}
       {h k : s ⇛rf Γ ； C} → h ≗rf k → 
       {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} →
        ++rf Δ₀ Ξ s h gs ≗rf ++rf Δ₀ Ξ s k gs
++rf≗₁ refl = refl
++rf≗₁ (~ eq) = ~ (++rf≗₁ eq)
++rf≗₁ (eq • eq₁) = (++rf≗₁ eq) • (++rf≗₁ eq₁)
++rf≗₁ (⊗r+ eq eqs) = ⊗r+ eq (++≗s₁ eqs)

++rf≗₂ : ∀ {Δ₀ Γ B₀ C Ξ s}
         (h : s ⇛rf Γ ； C) → 
         {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → fs ≗s⇑ gs → 
         ++rf Δ₀ Ξ s h fs ≗rf ++rf Δ₀ Ξ s h gs
++rf≗₂ Ir eqs = ⊗r+ refl eqs
++rf≗₂ (⊗r+ Δ₀ Ξ m h gs eq) eqs = ⊗r+ refl (++≗s₂ gs eqs)
++rf≗₂ blurr eqs = ⊗r+ refl eqs


-- lf∙→∘at : ∀ {T Γ X} (x : isAt X)
--   →  (f : [ ∘ , ∙ ] T ∣ Γ ⇓ X)
--   → [ ∘ , ∘ ] T ∣ Γ ⇓ X
-- lf∙→∘at x (focl q lf ax refl) = focl q lf (focr _ blurr ax refl) refl
-- lf∙→∘at x (focl q lf (unfoc (inj₁ ok) f) eq) = focl q lf (unfoc ok f) eq
-- lf∙→∘at x (focl q lf (unfoc (inj₂ ok) f) eq) = ⊥-elim (neg×posat→⊥ ok (at→posat x))
-- lf∙→∘at x (unfoc ok f) = ⊥-elim (neg×posat→⊥ ok (at→posat x))

-- early-rf-at : ∀ {T Γ₁ Γ₂ Δ X Q R} t {x} {q : isPos Q} {r}
--             {rf : just (X , at→negat x) ⇛rf Γ₂ ； R}
--             {f : [ ∘ , ∙ ] T ∣ Δ ++ Γ₁ ⇓ X} (ℓ : L T Δ Q) →
--             unfoc {∙}{∘} q (runL {Δ = Γ₁ ++ Γ₂} ℓ (foc t r (focr {Γ₀ = Δ ++ Γ₁}{Γ₂}_ rf f refl)))
--               ≗⇓ focr _ rf (unfoc (inj₁ q) (runL {Δ = Γ₁} ℓ (foc t (at→posat x) (lf∙→∘at x f)))) refl

early-rf⇓-at : ∀ {S Γ₀ Δ Δ₀ X P B₀ p s Ξ}
  → (x : isAt X)
  → (f : [ ∘ , ∘ ] S ∣ Δ ++ Γ₀ ⇓ X)
  → {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)}
  → (ℓ : L S Δ P)
  → unfoc {∙}{∘} p (runL {Δ = Γ₀ ++ Δ₀ ++ concat (cxts Ξ)} ℓ (foc s (isPosAt⊗⋆ tt (fmas Ξ)) (⊗r+⇓Q Δ₀ (at→posat x) Ξ f gs)))
         ≗⇓ focr {Γ₀ = Γ₀} (just (_ , at→negat x)) (⊗r+ Δ₀ Ξ (negat→isn't⊗ (at→negat x)) blurr gs refl) (unfoc (inj₁ p) (runL {Δ = Γ₀} ℓ (foc s (at→posat x) f))) refl


early-rf⇑-at : ∀ {S Γ₀ Δ Γ Δ₀ X P B₀ p Ξ}
  → (x : isAt X)
  → (f : S ∣ Γ ⇑ X)
  → {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)}
  → (eq : Γ ≡ Δ ++ Γ₀)
  → (ℓ : L S Δ P)
  → unfoc {∙}{∘} p (runL {Δ = Γ₀ ++ Δ₀ ++ concat (cxts Ξ)} ℓ (⊗r+⇑Q Δ₀ (at→posat x) Ξ (subst⇑ f eq) gs))
         ≗⇓ focr {Γ₀ = Γ₀} (just (_ , at→negat x)) (⊗r+ Δ₀ Ξ (negat→isn't⊗ (at→negat x)) blurr gs refl) (unfoc (inj₁ p) (runL {Δ = Γ₀} ℓ (subst⇑ f eq))) refl

early-rf⇑-at x (Il q f) refl ℓ =
  unfoc (refl⇑ (cong (runL ℓ) (sym (Il⇑eq _))))
  • early-rf⇑-at x f refl (Il-1 ℓ)
  • focr refl (unfoc (refl⇑ (cong (runL ℓ) (Il⇑eq _))))
early-rf⇑-at x (⊗l q f) refl ℓ = 
  unfoc (refl⇑ (cong (runL ℓ) (sym (⊗l⇑eq _))))
  • early-rf⇑-at x f refl (⊗l-1 ℓ)
  • focr refl (unfoc (refl⇑ (cong (runL ℓ) (⊗l⇑eq _))))
early-rf⇑-at {X = ` X} x (foc s q f) refl ℓ = early-rf⇓-at x f ℓ

early-rf⇓-at x (focl q lf (focr (just _) (⊗r+ Δ₀ Ξ m rf gs eq₁) ax refl) eq) ℓ = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))
early-rf⇓-at x (focl q lf (focr (just (M , m)) (⊗r+ Δ₀ Ξ m₁ rf gs eq₂) (unfoc ok f) eq₁) eq) ℓ = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))
early-rf⇓-at {p = p} {s = s} {Ξ} x (focl {Q} q lf (focr (just (` X , tt)) blurr f refl) eq) ℓ = 
  unfoc (congrunL ℓ (foc-same (swap' eq)))
  • early-rf-at s ℓ
  • focr refl (unfoc (congrunL ℓ (foc (~ swap' eq))))
early-rf⇓-at {Δ₀ = Δ₀} {X = ` X} {s = s} {Ξ} x (focl q lf (unfoc ok f) eq) ℓ = 
  unfoc (congrunL ℓ (foc-same (focl refl {eq' = cong (λ a → a ++ Δ₀ ++ concat (cxts Ξ)) eq} (early-rf⇑-at tt f refl done) • swap' eq)))
  • early-rf-at s ℓ
  • focr refl (unfoc (congrunL ℓ (foc-same (~ swap' eq {eq} • focl refl blurr-at))))

early-rf⇓-at x (focr ─ (⊗r+ Δ₀ Ξ m rf gs eq₁) f eq) ℓ = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))
early-rf⇓-at x (focr (just (M , m)) (⊗r+ Δ₀ Ξ m₁ rf' gs eq₁) f eq) ℓ = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))
early-rf⇓-at {s = s} x (focr (just (` X , _)) blurr f refl) ℓ = early-rf-at s ℓ




early-rf⇑N : ∀ {S Γ₀ Δ Γ Γ₁ Δ₀ A P B₀ n p Ξ}
 → (f : S ∣ Γ ⇑ A)
 → {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)}
 → {eq : Γ ≡ Δ ++ Γ₀ ++ Γ₁}
 → (ℓ : L S Δ P)
 → unfoc {∙}{∘} p (runL {Δ = Γ₀ ++ Δ₀ ++ concat (cxts Ξ)} ℓ (⊗r+⇑N {Γ₀ = Δ ++ Γ₀} Γ₁ Δ₀ n Ξ f gs eq))
         ≗⇓ focr {Γ₀ = Γ₀} (just (_ , neg→negat n)) (⊗r+ Δ₀ Ξ (neg→isn't⊗ n) blurr gs refl) (unfoc (inj₁ p) (runL {Δ = Γ₀} ℓ (⊸r⋆⇑ Γ₁ (subst⇑ f eq)))) refl
early-rf⇑N {Γ₁ = Γ₁} (⊸r f) {eq = refl} ℓ =
  early-rf⇑N f ℓ • focr refl (unfoc (refl⇑ (cong (runL ℓ) (⊸r⋆⊸r⋆⇑ Γ₁ {_ ∷ []}))))
early-rf⇑N {Γ₁ = Γ₁} (Il q f) {eq = refl} ℓ =
  unfoc (refl⇑ (cong (runL ℓ) (sym (Il⇑eq _))))
  • early-rf⇑N f (Il-1 ℓ)
  • focr refl (unfoc (refl⇑ (cong (runL ℓ) (trans (sym (⊸r⋆Il⇑ Γ₁)) (cong (⊸r⋆⇑ Γ₁) (Il⇑eq f))))))
early-rf⇑N {Γ₁ = Γ₁} (⊗l q f) {eq = refl} ℓ =
  unfoc (refl⇑ (cong (runL ℓ) (sym (⊗l⇑eq _))))
  • early-rf⇑N f (⊗l-1 ℓ)
  • focr refl (unfoc (refl⇑ (cong (runL ℓ) (trans (sym (⊸r⋆⊗l⇑ Γ₁)) (cong (⊸r⋆⇑ Γ₁) (⊗l⇑eq f))))))
early-rf⇑N (foc s q f) {eq = refl} ℓ = early-rf s ℓ 

cong⊗r+⇑Q₁ : ∀ {S Γ Δ₀ B₀ Q q Ξ}
             {f f' : S ∣ Γ ⇑ Q} → f ≗⇑ f' →
             {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → 
       ---------------------------------------------------------------------
           ⊗r+⇑Q Δ₀ q Ξ f gs ≗⇑ ⊗r+⇑Q Δ₀ q Ξ f' gs

cong⊗r+⇓Q₁ refl = refl
cong⊗r+⇓Q₁ (~ eq) = ~ (cong⊗r+⇓Q₁ eq)
cong⊗r+⇓Q₁ (eq • eq₁) = (cong⊗r+⇓Q₁ eq) • (cong⊗r+⇓Q₁ eq₁)
cong⊗r+⇓Q₁ (focl eql eq) = focl eql (cong⊗r+⇓Q₁ eq)
cong⊗r+⇓Q₁ (focr eqr eq) = focr (++rf≗₁ eqr) eq
cong⊗r+⇓Q₁ (focrn eqr) = focrn (++rf≗₁ eqr)
cong⊗r+⇓Q₁ {∙} {just P} (unfoc eq) = unfoc (cong⊗r+⇑Q₁ eq)
cong⊗r+⇓Q₁ swap = swap
cong⊗r+⇓Q₁ (early-rf t ℓ {eq = refl}) = unfoc (refl⇑ (runL⊗r+⇑Q ℓ)) • early-rf t ℓ
cong⊗r+⇓Q₁ (early-rf-at t ℓ {eq = refl}) = unfoc (refl⇑ (runL⊗r+⇑Q ℓ)) • early-rf-at t ℓ
cong⊗r+⇓Q₁ (blurr-at {f = f}) = ~ early-rf⇑-at tt f refl done


cong⊗r+⇑Q₁ refl = refl
cong⊗r+⇑Q₁ (~ eq) = ~ (cong⊗r+⇑Q₁ eq)
cong⊗r+⇑Q₁ (eq • eq₁) = (cong⊗r+⇑Q₁ eq) • (cong⊗r+⇑Q₁ eq₁)
cong⊗r+⇑Q₁ (Il eq) = Il (cong⊗r+⇑Q₁ eq)
cong⊗r+⇑Q₁ (⊗l eq) = ⊗l (cong⊗r+⇑Q₁ eq)
cong⊗r+⇑Q₁ (foc eq) = foc (cong⊗r+⇓Q₁ eq)

cong⊗r+⇓Q₂ : ∀ {b S Γ Δ₀ B₀ Q q Ξ}
             (f : [ b , ∘ ] S ∣ Γ ⇓ Q) → 
             {gs gs' : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → gs ≗s⇑ gs' →  
       ---------------------------------------------------------------------
           ⊗r+⇓Q Δ₀ q Ξ f gs ≗⇓ ⊗r+⇓Q Δ₀ q Ξ f gs'

cong⊗r+⇑Q₂ : ∀ {S Γ Δ₀ B₀ Q q Ξ}
             (f : S ∣ Γ ⇑ Q) → 
             {gs gs' : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → gs ≗s⇑ gs' →  
       ---------------------------------------------------------------------
           ⊗r+⇑Q Δ₀ q Ξ f gs ≗⇑ ⊗r+⇑Q Δ₀ q Ξ f gs'

cong⊗r+⇓Q₂ (focl q lf f eq) eqs = focl refl (cong⊗r+⇓Q₂ f eqs)
cong⊗r+⇓Q₂ (focr (just _) rf f eq) eqs = focr (++rf≗₂ rf eqs) refl
cong⊗r+⇓Q₂ (focr ─ rf f eq) eqs = focrn (++rf≗₂ rf eqs)
cong⊗r+⇓Q₂ {∙} {just P} (unfoc ok f) eqs = unfoc (cong⊗r+⇑Q₂ f eqs)

cong⊗r+⇑Q₂ (Il q f) eqs = Il (cong⊗r+⇑Q₂ f eqs)
cong⊗r+⇑Q₂ (⊗l q f) eqs = ⊗l (cong⊗r+⇑Q₂ f eqs)
cong⊗r+⇑Q₂ (foc s q f) eqs = foc (cong⊗r+⇓Q₂ f eqs)

cong⊗r+⇑Q : ∀ {S Γ Δ₀ B₀ Q q Ξ}
             {f f' : S ∣ Γ ⇑ Q} → f ≗⇑ f' →
             {gs gs' : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → gs ≗s⇑ gs' →  
       ---------------------------------------------------------------------
           ⊗r+⇑Q Δ₀ q Ξ f gs ≗⇑ ⊗r+⇑Q Δ₀ q Ξ f' gs'
cong⊗r+⇑Q {f' = f'} eq eqs = cong⊗r+⇑Q₁ eq • cong⊗r+⇑Q₂ f' eqs 

cong⊗r+⇑N₁ : ∀ {S Γ₀ Γ Γ₁ Δ₀ A B₀ n Ξ}
           {f g : S ∣ Γ ⇑ A} → f ≗⇑ g → 
           {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)}
           {eq : Γ ≡ Γ₀ ++ Γ₁} →
           ⊗r+⇑N Γ₁ Δ₀ n Ξ f gs eq ≗⇑ ⊗r+⇑N Γ₁ Δ₀ n Ξ g gs eq
cong⊗r+⇑N₁ refl {eq = refl} = refl
cong⊗r+⇑N₁ (~ eq) = ~ (cong⊗r+⇑N₁ eq)
cong⊗r+⇑N₁ (eq • eq₁) = cong⊗r+⇑N₁ eq • cong⊗r+⇑N₁ eq₁
cong⊗r+⇑N₁ (⊸r eq) {eq = refl} = cong⊗r+⇑N₁ eq
cong⊗r+⇑N₁ (Il eq) = Il (cong⊗r+⇑N₁ eq)
cong⊗r+⇑N₁ (⊗l eq) {eq = refl} = ⊗l (cong⊗r+⇑N₁ eq)
cong⊗r+⇑N₁ {Γ₁ = Γ₁} (foc eq) {eq = refl} = foc (focr refl (unfoc (cong⊸r⋆⇑ Γ₁ (foc eq))))

cong⊗r+⇑N₂ : ∀ {S Γ₀ Γ Γ₁ Δ₀ A B₀ n Ξ}
           (f : S ∣ Γ ⇑ A) → 
           {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → fs ≗s⇑ gs → 
           {eq : Γ ≡ Γ₀ ++ Γ₁} →
           ⊗r+⇑N Γ₁ Δ₀ n Ξ f fs eq ≗⇑ ⊗r+⇑N Γ₁ Δ₀ n Ξ f gs eq
cong⊗r+⇑N₂ (⊸r f) eqs {refl} = cong⊗r+⇑N₂ f eqs
cong⊗r+⇑N₂ (Il q f) eqs {eq} = Il (cong⊗r+⇑N₂ f eqs)
cong⊗r+⇑N₂ (⊗l q f) eqs {refl} = ⊗l (cong⊗r+⇑N₂ f eqs)
cong⊗r+⇑N₂ (foc s q f) eqs {refl} = foc (focr (⊗r+ refl eqs) refl)

cong⊗r+⇑N : ∀ {S Γ₀ Γ Γ₁ Δ₀ A B₀ n Ξ}
           {f g : S ∣ Γ ⇑ A} → f ≗⇑ g → 
           {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → fs ≗s⇑ gs → 
           {eq : Γ ≡ Γ₀ ++ Γ₁} →
           ⊗r+⇑N Γ₁ Δ₀ n Ξ f fs eq ≗⇑ ⊗r+⇑N Γ₁ Δ₀ n Ξ g gs eq
cong⊗r+⇑N {g = g} eq eqs = cong⊗r+⇑N₁ eq • cong⊗r+⇑N₂ g eqs

cong⊗r+⇑ : {S : Stp} {Γ : Cxt} {Δ₀ : Cxt} {B₀ A : Fma}
           {Ξ : List (Cxt × Fma)}
           {f f' : S ∣ Γ ⇑ A} → f ≗⇑ f' →
           {gs gs' : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → gs ≗s⇑ gs' → 
    ---------------------------------------------------------------------
          ⊗r+⇑ Δ₀ Ξ f gs ≗⇑ ⊗r+⇑ Δ₀ Ξ f' gs'
cong⊗r+⇑ {A = ` X} eq eqs = cong⊗r+⇑Q eq eqs
cong⊗r+⇑ {A = I} eq eqs = cong⊗r+⇑Q eq eqs
cong⊗r+⇑ {A = A ⊗ B} eq eqs = cong⊗r+⇑Q eq eqs
cong⊗r+⇑ {A = A ⊸ B} eq eqs = cong⊗r+⇑N eq eqs

⊗r+⇓Qpass⇓ : ∀ {Γ Δ₀ A B₀ Q q Ξ}
             (f : [ ∘ , ∘ ] just A ∣ Γ ⇓ Q)
             {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} →
             ⊗r+⇓Q Δ₀ q Ξ (pass⇓ f) gs ≗⇓ pass⇓ (⊗r+⇓Q Δ₀ q Ξ f gs)

⊗r+⇑Qpass⇑ : ∀ {Γ Δ₀ A B₀ Q q Ξ}
             (f : just A ∣ Γ ⇑ Q)
             {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} →
             ⊗r+⇑Q Δ₀ q Ξ (pass⇑ f) gs ≗⇑ pass⇑ (⊗r+⇑Q Δ₀ q Ξ f gs)

⊗r+⇓Qpass⇓ (focl q lf f refl) = refl
⊗r+⇓Qpass⇓ (focr (just x) rf f refl) = refl

⊗r+⇑Qpass⇑ (Il q f) = refl
⊗r+⇑Qpass⇑ (⊗l q f) = refl
⊗r+⇑Qpass⇑ (foc s q f) = foc (⊗r+⇓Qpass⇓ f)


⊗r+⇑Npass⇑ : ∀ {Γ₀ Γ Γ₁ Δ₀ A A' B₀ n Ξ}
           (f : just A' ∣ Γ ⇑ A)
           {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)}
           {eq : Γ ≡ Γ₀ ++ Γ₁} →
           ⊗r+⇑N Γ₁ Δ₀ n Ξ (pass⇑ f) gs (cong (A' ∷_) eq) ≗⇑ pass⇑ (⊗r+⇑N Γ₁ Δ₀ n Ξ f gs eq)
⊗r+⇑Npass⇑ (⊸r f) {eq = refl} = ⊗r+⇑Npass⇑ f
⊗r+⇑Npass⇑ {Γ₁ = Γ₁} {Ξ = Ξ} (Il q f) {eq = refl} =
  foc (focr refl (early-lf _ q)
       • ~ swap
       • focl refl (focr refl (unfoc (refl⇑ (trans (cong (⊸r⋆⇑ Γ₁) (sym (Il⇑eq f))) (⊸r⋆Il⇑ Γ₁))))
                              • ~ early-rf⇑N f (Il-1 done)
                              • unfoc (refl⇑ (Il⇑eq _))))
⊗r+⇑Npass⇑ {Γ₁ = Γ₁} {Ξ = Ξ} (⊗l q f) {eq = refl} =
  foc (focr refl (early-lf _ q)
       • ~ swap
       • focl refl (focr refl (unfoc (refl⇑ (trans (cong (⊸r⋆⇑ Γ₁) (sym (⊗l⇑eq f))) (⊸r⋆⊗l⇑ Γ₁))))
                               • ~ early-rf⇑N f (⊗l-1 done)
                               • unfoc (refl⇑ (⊗l⇑eq _))))
⊗r+⇑Npass⇑ {Γ₁ = Γ₁} (foc s q f) {eq = refl} =
  foc (focr refl (unfoc (refl⇑ (sym (pass⊸r⋆⇑ Γ₁)))))

⊗r+pass⇑ : ∀ {Γ Δ₀ A B₀ C Ξ}
             {f : just A ∣ Γ ⇑ C}
             {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} →
             ⊗r+⇑ Δ₀ Ξ (pass⇑ f) gs ≗⇑ pass⇑ (⊗r+⇑ Δ₀ Ξ f gs)
⊗r+pass⇑ {C = ` X} = ⊗r+⇑Qpass⇑ _
⊗r+pass⇑ {C = I} = ⊗r+⇑Qpass⇑ _
⊗r+pass⇑ {C = C ⊗ C₁} = ⊗r+⇑Qpass⇑ _
⊗r+pass⇑ {C = C ⊸ C₁} {f = f} = ⊗r+⇑Npass⇑ f

⊗rpass⇑ : ∀ {Γ Δ A' A B}
          {f : just A' ∣ Γ ⇑ A}
          {g : ─ ∣ Δ ⇑ B} → 
          ⊗r⇑ (pass⇑ f) g ≗⇑ pass⇑ (⊗r⇑ f g)
⊗rpass⇑ = ⊗r+pass⇑ {gs = _ ∷ []}

focus≗ : ∀ {S Γ A} {f g : S ∣ Γ ⊢ A}
  → f ≗ g → focus f ≗⇑ focus g
focus≗ refl = refl
focus≗ (~ eq) = ~ (focus≗ eq)
focus≗ (eq ∙ eq₁) = (focus≗ eq) • (focus≗ eq₁)
focus≗ (pass eq) = congpass⇑ (focus≗ eq)
focus≗ (Il eq) = congIl⇑ (focus≗ eq) 
focus≗ (⊗l eq) = cong⊗l⇑ (focus≗ eq)  
focus≗ (⊗r eq eq₁) = cong⊗r+⇑ (focus≗ eq) (focus≗ eq₁ ∷ []) 
focus≗ (⊸r eq) = ⊸r (focus≗ eq)
focus≗ (⊸l eq eq₁) = {!!} 
focus≗ (⊗rIl {Δ = Δ}) = refl⇑ (⊗r+Il⇑ Δ [] _ _)
focus≗ (⊗r⊗l {Δ = Δ}) = refl⇑ (⊗r+⊗l⇑ Δ [] _ _)
focus≗ ⊸rpass = refl
focus≗ ⊸rIl = refl
focus≗ ⊸r⊗l = refl
focus≗ ⊸r⊸l = refl⇑ (⊸r⊸l⇑ _ _)

focus≗ ⊗rpass = ⊗rpass⇑
focus≗ ⊗r⊸l = {!!}


focus∘emb⇑ : ∀ {S Γ A} (f : S ∣ Γ ⇑ A) → focus (emb⇑ f) ≗⇑ f
focus∘emb⇓ : ∀ {S Γ Q} (s : isIrr S) (q : isPosAt Q)
  → (f : [ ∘ , ∘ ] S ∣ Γ ⇓ Q) → focus (emb⇓ f) ≗⇑ foc s q f

focus∘emb⇑ (⊸r f) = ⊸r (focus∘emb⇑ f)
focus∘emb⇑ (Il q f) = refl⇑ (Il⇑eq {q = q} _) • Il (focus∘emb⇑ f)
focus∘emb⇑ (⊗l q f) = refl⇑ (⊗l⇑eq {q = q} _) • ⊗l (focus∘emb⇑ f)
focus∘emb⇑ (foc s q f) = focus∘emb⇓ s q f 

focus∘emb⇓ s q (focl q₁ (pass (⊸l+ Γ₀ Ξ q₂ fs blurl refl)) f refl) = {!fs!}
focus∘emb⇓ s q (focl q₁ (pass blurl) (focr s₁ (⊗r+ Δ₀ Ξ m (⊗r+ Δ₁ Ξ₁ m₁ rf gs₁ eq₂) gs eq₁) f eq) refl) = ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ _ (fmas Ξ₁)) m)
focus∘emb⇓ s q (focl q₁ (pass blurl) (focr .(just (` _ , _)) (⊗r+ Δ₀ Ξ m blurr gs refl) ax refl) refl) = {!swapped!}
focus∘emb⇓ s q (focl q₁ (pass blurl) (focr .(just (_ , _)) (⊗r+ Δ₀ Ξ m blurr gs refl) (unfoc ok f) refl) refl) = {!swapped!}
focus∘emb⇓ s q (focl q₁ (pass blurl) (focr .(just (` _ , _)) blurr ax refl) refl) =
  foc (focl refl (~ {!!}))
focus∘emb⇓ s q (focl q₁ (pass blurl) (focr .(just (_ , _)) blurr (unfoc ok f) refl) refl) = {!!}
focus∘emb⇓ s q (focl q₁ (pass blurl) (unfoc ok f) refl) = {!!}
focus∘emb⇓ s q (focl q₁ (⊸l+ Γ₀ Ξ q₂ fs blurl refl) f refl) = {!!}
focus∘emb⇓ s q (focl q₁ blurl f refl) = {!!}
focus∘emb⇓ s q (focr (just _) (⊗r+ Δ₀ Ξ m (⊗r+ Δ₁ Ξ₁ m₁ rf gs₁ eq₂) gs eq₁) f eq) =
  ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ tt (fmas Ξ₁)) m)
focus∘emb⇓ s q (focr (just _) (⊗r+ Δ₀ Ξ m blurr gs refl) f refl) = {!!}
focus∘emb⇓ s q (focr (just _) blurr (focl q₁ lf f eq) refl) = {!!}
focus∘emb⇓ s q (focr (just _) blurr (unfoc ok f) refl) = {!imp!}
focus∘emb⇓ s q (focr ─ Ir (refl , refl) refl) = refl
focus∘emb⇓ s q (focr ─ (⊗r+ Δ₀ Ξ m Ir gs refl) (refl , refl) refl) = {!!}
focus∘emb⇓ s q (focr ─ (⊗r+ Δ₀ Ξ m (⊗r+ Δ₁ Ξ₁ m₁ rf gs₁ eq₂) gs eq₁) f eq) =
  ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ tt (fmas Ξ₁)) m)
