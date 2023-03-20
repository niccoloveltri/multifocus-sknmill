{-# OPTIONS --rewriting #-}

module MultifocSeqCalc where

open import Data.List 
open import Data.List.Relation.Unary.All hiding (map)
open import Data.Maybe hiding (map)
open import Data.Sum hiding (map; swap)
open import Data.Product renaming (map to map×) hiding (swap)
open import Data.Unit
open import Data.Empty
open import Data.Bool renaming (true to ∙; false to ∘)
open import Relation.Binary.PropositionalEquality hiding (_≗_)

open import Utilities
open import Formulae
open import SeqCalc

-- Multi-focused sequent calculus

-- The side condition for releasing focus:
-- -- if only left-focusing happened, stoup formula should be positive;
-- -- if only right-focusing happened, succedent formula should be negative;
-- -- if both left- and right-focusing happened, either stoup formula
-- -- is positive or succedent formula is negative.
UT : Bool → Bool → Stp → Fma → Set
UT ∘ ∘ _ _ = ⊥
UT ∙ ∘ (just A) C = isPos A 
UT ∙ ∘ ─ C = ⊥
UT ∘ ∙ S C = isNeg C 
UT ∙ ∙ (just A) C = isPos A ⊎ isNeg C
UT ∙ ∙ ─ C = ⊥

-- A predicate lifting employed in the focR rule
end-rf? : (P : Stp → Cxt → Fma → Set) → Stp → Cxt → Maybe (Σ Fma isNegAt) → Set
end-rf? P S Γ (just (M , m)) = P S Γ M
end-rf? P S Γ ─ = S ≡ nothing × Γ ≡ []

-- ================================================

-- Inference rules 

-- -- Differently from the paper, here we have macro rules ⊸l+ and ⊗r+
-- -- in phase lf and rf respectively. This facilitates the
-- -- construction of the focusing function.

-- -- The Booleans in phase ⇓ indicate whether the stoup formula
-- -- and/or the succedent formula have been blurred.


data _∣_⇑_ : Stp → Cxt → Fma → Set
data [_,_]_∣_⇓_ : Bool → Bool → Stp → Cxt → Fma → Set
data _⇛lf_；_ {Q : Fma} (q : isPosAt Q) : Stp → Cxt → Set
data _⇛rf_；_  : Maybe (Σ Fma isNegAt) → Cxt → Fma → Set

data _∣_⇑_ where

  ⊸r : {S : Stp} {Γ : Cxt} {A B : Fma} 
         (f : S ∣ Γ ∷ʳ A ⇑ B) →
       ---------------------------------
             S ∣ Γ ⇑ A ⊸ B

  Il : {Γ : Cxt} {Q : Fma}
       (q : isPosAt Q)
       (f :  ─ ∣ Γ ⇑ Q) →
    -------------------------
       just I ∣ Γ ⇑ Q

  ⊗l : {Γ : Cxt} {A B Q : Fma}
       (q : isPosAt Q)
       (f : just A ∣ B ∷ Γ ⇑ Q) →
    -------------------------------------
         just (A ⊗ B) ∣ Γ ⇑ Q

  foc : {S : Stp} {Γ : Cxt} {Q : Fma}
        (s : isIrr S) (q : isPosAt Q)
        (f : [ ∘ , ∘ ] S ∣ Γ ⇓ Q) → 
      ------------------------------------
             S ∣ Γ ⇑ Q

data [_,_]_∣_⇓_ where

  ax : {X : At} → [ ∙ , ∙ ] just (` X) ∣ [] ⇓ ` X
  -- {b b' : Bool} {X : At} → [ b , b' ] just (` X) ∣ [] ⇓ ` X

  focl : {b : Bool} {S : Stp} {Γ Γ₀ Γ₁ : Cxt} {C Q : Fma}
         (q : isPosAt Q)
         (lf : q ⇛lf S ； Γ₀)
         (f : [ ∙ , b ] just Q ∣ Γ₁ ⇓ C)          
         (eq : Γ ≡ Γ₀ ++ Γ₁) → 
      ------------------------------------
          [ ∘ , b ] S ∣ Γ ⇓ C

  focr : {b : Bool} {S : Stp} {Γ Γ₀ Γ₁ : Cxt} {C : Fma}
         (s : Maybe (Σ Fma isNegAt))
         (rf : s ⇛rf Γ₁ ； C) → 
         (f : end-rf? (λ T Γ A → [ b , ∙ ] T ∣ Γ ⇓ A) S Γ₀ s) → 
         (eq : Γ ≡ Γ₀ ++ Γ₁) → 
      ------------------------------------
           [ b , ∘ ] S ∣ Γ ⇓ C

  unfoc : {b b' : Bool} {S : Stp} {Γ : Cxt} {C : Fma}
          (ok : UT b b' S C)
          (f : S ∣ Γ ⇑ C) →
      ------------------------------------
          [ b , b' ] S ∣ Γ ⇓ C

data _⇛lf_；_ {Q} q' where

  pass : {Γ : Cxt} {A : Fma}
         (f : q' ⇛lf just A ； Γ) →
     ----------------------------------
         q' ⇛lf ─ ； (A ∷ Γ)

  ⊸l+ : (Γ₀ : Cxt) {Δ Γ' : Cxt} {A₀ Q : Fma}
         (Ξ : List (Cxt × Fma))
         (q : isPosAt Q)
         (fs : All (λ ΓA → ─ ∣ proj₁ ΓA ⇑ proj₂ ΓA) ((Γ₀ , A₀) ∷ Ξ))
         (g : q' ⇛lf just Q ； Δ) →
         (eq : Γ' ≡ Γ₀ ++ concat (cxts Ξ) ++ Δ) → 
      ----------------------------------------------------------
        q' ⇛lf just ((A₀ ∷ fmas Ξ) ⊸⋆ Q) ； Γ'

  blurl : q' ⇛lf just Q ； []

data _⇛rf_；_ where

  Ir : nothing ⇛rf [] ； I

  ⊗r+ : ∀ {Γ Γ' : Cxt} (Δ₀ : Cxt) {M B₀ : Fma} {s}
        (Ξ : List (Cxt × Fma))
        (m : isn't⊗ M)
        (f : s ⇛rf Γ ； M)
        (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ))
        (eq : Γ' ≡ Γ ++ Δ₀ ++ concat (cxts Ξ)) →
      ------------------------------------
         s ⇛rf Γ' ； M ⊗⋆ (B₀ ∷ fmas Ξ)

  blurr : {M : Fma} {m : isNegAt M} → 
         just (M , m) ⇛rf [] ； M

subst⇑ : ∀ {S Γ Δ A} (f : S ∣ Γ ⇑ A) (eq : Γ ≡ Δ) → S ∣ Δ ⇑ A
subst⇑ f refl = f

-- =========================================

-- Embedding into sequent calculus derivations (in Theorem 1)

emb⇑ : ∀ {S Γ A} → S ∣ Γ ⇑ A → S ∣ Γ ⊢ A
emb⇓ : ∀ {b b' S Γ A} → [ b , b' ] S ∣ Γ ⇓ A → S ∣ Γ ⊢ A
embs⇑ : ∀ {Ξ} → All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ
  → All (λ ΔB → ─ ∣ proj₁ ΔB ⊢ proj₂ ΔB) Ξ

emb⇑ (⊸r f) = ⊸r (emb⇑ f)
emb⇑ (Il q f) = Il (emb⇑ f)
emb⇑ (⊗l q f) = ⊗l (emb⇑ f)
emb⇑ (foc s q f) = emb⇓ f

emb⇓ ax = ax
emb⇓ (focl q (pass (⊸l+ Γ₀ Ξ q₁ fs blurl refl)) f refl) =
  pass (⊸l⋆ {Ξ = (Γ₀ , _) ∷ Ξ} (embs⇑ fs) (emb⇓ f))
emb⇓ (focl q (pass blurl) f refl) = pass (emb⇓ f)
emb⇓ (focl q (⊸l+ Γ₀ Ξ q₁ fs blurl refl) f refl) =
  ⊸l⋆ {Ξ = (Γ₀ , _) ∷ Ξ} (embs⇑ fs) (emb⇓ f)
emb⇓ (focl q blurl f refl) = emb⇓ f
emb⇓ (focr .─ Ir (refl , refl) refl) = Ir
emb⇓ (focr (just _) (⊗r+ Δ₀ Ξ m (⊗r+ Δ₁ Ξ₁ m₁ rf gs₁ eq) gs refl) f refl) =
  ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ tt (fmas Ξ₁)) m)
emb⇓ (focr (just _) (⊗r+ Δ₀ Ξ m blurr gs refl) f refl) =
  ⊗r⋆ {Ξ = (Δ₀ , _) ∷ Ξ} (emb⇓ f) (embs⇑ gs)
emb⇓ (focr ─ (⊗r+ Δ₀ Ξ m Ir gs refl) (refl , refl) refl) =
  ⊗r⋆ {Ξ = (Δ₀ , _) ∷ Ξ} Ir (embs⇑ gs)
emb⇓ (focr ─ (⊗r+ Δ₀ Ξ m (⊗r+ Δ₁ Ξ₁ m₁ rf gs₁ eq₁) gs eq) (refl , refl) refl) =
  ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ tt (fmas Ξ₁)) m)
emb⇓ (focr .(just (_ , _)) blurr f refl) = emb⇓ f
emb⇓ (unfoc ok f) = emb⇑ f

embs⇑ [] = []
embs⇑ (f ∷ fs) = emb⇑ f ∷ embs⇑ fs

-- ==========================================

-- Some useful lemmata:

-- -- Concatenation of two right-focusing phases

++rf : (Δ₀ : Cxt) {Γ : Cxt} {B₀ C : Fma} (Ξ : List (Cxt × Fma))
       (s : Maybe (Σ Fma isNegAt))
       (rf : s ⇛rf Γ ； C)
       (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)) →
       s ⇛rf Γ ++ Δ₀ ++ concat (cxts Ξ) ； C ⊗⋆ (B₀ ∷ fmas Ξ)
++rf Δ₀ Ξ .─ Ir gs = ⊗r+ Δ₀ Ξ tt Ir gs refl
++rf Δ₀ Ξ s (⊗r+ {Γ} Δ₁ Ξ₁ m rf gs₁ eq) gs = 
  ⊗r+ Δ₁ (Ξ₁ ++ (Δ₀ , _) ∷ Ξ) m rf (gs₁ ++All gs)
      (trans (cong (_++ Δ₀ ++ concat (cxts Ξ)) eq)
             (cong (λ x → Γ ++ Δ₁ ++ x) (sym (concat++ (cxts Ξ₁) (_ ∷ cxts Ξ))))) 
++rf Δ₀ Ξ (just (_ , m)) blurr gs = ⊗r+ Δ₀ Ξ (negat→isn't⊗ m) blurr gs refl

-- ==========================================

-- All rules of the sequent calculus are admissible

-- -- Iterated ⊸-right

⊸r⋆⇑ : {S : Stp} {Γ : Cxt} (Δ : Cxt) {A : Fma}
      (f : S ∣ Γ ++ Δ ⇑ A) →
  --------------------------------------------
        S ∣ Γ ⇑ Δ ⊸⋆ A
⊸r⋆⇑ [] f = f
⊸r⋆⇑ (A' ∷ Δ) f = ⊸r (⊸r⋆⇑ Δ f) 

-- -- Left invertible rules

Il⇑ : {Γ : Cxt} {C : Fma}
     (f :  ─ ∣ Γ ⇑ C) →
  -------------------------
     just I ∣ Γ ⇑ C
Il⇑ (⊸r f) = ⊸r (Il⇑ f)
Il⇑ (foc s q f) = Il q (foc s q f)

⊗l⇑ : {Γ : Cxt} {A B C : Fma}
     (f : just A ∣ B ∷ Γ ⇑ C) →
  -------------------------------------
       just (A ⊗ B) ∣ Γ ⇑ C
⊗l⇑ (⊸r f) = ⊸r (⊗l⇑ f)
⊗l⇑ (Il q f) = ⊗l q (Il q f)
⊗l⇑ (⊗l q f) = ⊗l q (⊗l q f)
⊗l⇑ (foc s q f) = ⊗l q (foc s q f)

-- -- Accumulator of left invertible rules
data L : Stp → Cxt → Fma → Set where
  done : ∀{A} → L (just A) [] A
  Il-1 : ∀{Γ C} → L (just I) Γ C → L nothing Γ C
  ⊗l-1 : ∀{Γ A B C} → L (just (A ⊗ B)) Γ C → L (just A) (B ∷ Γ) C

runLQ : ∀ {S Γ Δ A Q} (q : isPosAt Q) → L S Γ A
  → S ∣ Γ ++ Δ ⇑ Q → just A ∣ Δ ⇑ Q
runLQ q done f = f
runLQ q (Il-1 ℓ) f = runLQ q ℓ (Il q f)
runLQ q (⊗l-1 ℓ) f = runLQ q ℓ (⊗l q f)

runL : ∀ {S Γ Δ A C} → L S Γ A
  → S ∣ Γ ++ Δ ⇑ C → just A ∣ Δ ⇑ C
runL done f = f
runL (Il-1 ℓ) f = runL ℓ (Il⇑ f)
runL (⊗l-1 ℓ) f = runL ℓ (⊗l⇑ f)

-- -- Unit right

Ir⇑ : ─ ∣ [] ⇑ I
Ir⇑ = foc tt tt (focr nothing Ir (refl , refl) refl)

-- -- Axiom

ax⇑ : ∀ {X} → just (` X) ∣ [] ⇑ ` X
ax⇑ = foc tt tt (focl tt blurl (focr _ blurr ax refl) refl)

-- ax⇑ : ∀ {X} → just (` X) ∣ [] ⇑ ` X
-- ax⇑ = foc tt tt ax

-- -- Passivation

pass⇑ : {Γ : Cxt} {A C : Fma}
        (f : just A ∣ Γ ⇑ C) →
   ----------------------------------
          ─ ∣ A ∷ Γ ⇑ C
pass⇓ : {b : Bool} {Γ : Cxt} {A C : Fma}
         (f : [ ∘ , b ] just A ∣ Γ ⇓ C) →
   ----------------------------------
          [ ∘ , b ] ─ ∣ A ∷ Γ ⇓ C
pass⇑ (⊸r f) = ⊸r (pass⇑ f)
pass⇑ (Il q f) = foc tt q (focl tt (pass blurl) (unfoc tt (Il q f)) refl)
pass⇑ (⊗l q f) = foc tt q (focl tt (pass blurl) (unfoc tt (⊗l q f)) refl)
pass⇑ (foc s q f) = foc tt q (pass⇓ f)

pass⇓ (focl q lf f eq) = focl q (pass lf) f (cong (_ ∷_) eq)
pass⇓ (focr (just (M , m)) rf f eq) = focr (just (M , m)) rf (pass⇓ f) (cong (_ ∷_) eq)
pass⇓ {∙} (unfoc ok f) = unfoc ok (pass⇑ f)

-- -- (Iterated) ⊗-right

⊗r+⇓Q : {b : Bool} {S : Stp} {Γ : Cxt} (Δ₀ : Cxt) {B₀ P : Fma}
         (q : isPosAt P)
         (Ξ : List (Cxt × Fma))
         (f : [ b , ∘ ] S ∣ Γ ⇓ P)
         (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)) →  
    ---------------------------------------------------------------------
        [ b , ∘ ] S ∣ Γ ++ Δ₀ ++ concat (cxts Ξ) ⇓ P ⊗⋆ (B₀ ∷ fmas Ξ)

⊗r+⇑Q : {S : Stp} {Γ : Cxt} (Δ₀ : Cxt) {B₀ Q : Fma}
        (p : isPosAt Q)
        (Ξ : List (Cxt × Fma))
        (f : S ∣ Γ ⇑ Q)
        (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)) → 
    ---------------------------------------------------------------------
        S ∣ Γ ++ Δ₀ ++ concat (cxts Ξ) ⇑ Q ⊗⋆ (B₀ ∷ fmas Ξ)

⊗r+⇑Q Δ₀ p Ξ (Il q f) gs = Il (isPosAt⊗⋆ tt (fmas Ξ)) (⊗r+⇑Q Δ₀ p Ξ f gs)
⊗r+⇑Q Δ₀ p Ξ (⊗l q f) gs = ⊗l (isPosAt⊗⋆ tt (fmas Ξ)) (⊗r+⇑Q Δ₀ p Ξ f gs)
⊗r+⇑Q Δ₀ p Ξ (foc s q f) gs = foc s (isPosAt⊗⋆ tt (fmas Ξ)) (⊗r+⇓Q Δ₀ p Ξ f gs)

⊗r+⇓Q Δ₀ p Ξ (focl q lf f eq) gs =
  focl q lf (⊗r+⇓Q Δ₀ p Ξ f gs) (cong (_++ Δ₀ ++ concat (cxts Ξ)) eq)
⊗r+⇓Q Δ₀ p Ξ (focr s rf f eq) gs =
  focr s (++rf Δ₀ Ξ s rf gs) f (cong (_++ Δ₀ ++ concat (cxts Ξ)) eq)
⊗r+⇓Q {∙} {just P} Δ₀ q Ξ (unfoc ok f) gs = unfoc ok (⊗r+⇑Q Δ₀ q Ξ f gs)

⊗r+⇑N : {S : Stp} {Γ₀ Γ : Cxt} (Γ₁ Δ₀ : Cxt) {A B₀ : Fma}
         (n : isNeg (Γ₁ ⊸⋆ A))
         (Ξ : List (Cxt × Fma))
         (f : S ∣ Γ ⇑ A)
         (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ))
         (eq : Γ ≡ Γ₀ ++ Γ₁) →
    ---------------------------------------------------------------------
         S ∣ Γ₀ ++ Δ₀ ++ concat (cxts Ξ) ⇑ (Γ₁ ⊸⋆ A) ⊗⋆ (B₀ ∷ fmas Ξ)
⊗r+⇑N {Γ₀ = Γ₀} Γ₁ Δ₀ n Ξ (⊸r f) gs refl = ⊗r+⇑N {Γ₀ = Γ₀} (Γ₁ ∷ʳ _) Δ₀ n Ξ f gs refl
⊗r+⇑N Γ₁ Δ₀ n Ξ (Il q f) gs eq = Il (isPosAt⊗⋆ tt (fmas Ξ)) (⊗r+⇑N Γ₁ Δ₀ n Ξ f gs eq)
⊗r+⇑N Γ₁ Δ₀ n Ξ (⊗l q f) gs refl = ⊗l (isPosAt⊗⋆ tt (fmas Ξ)) (⊗r+⇑N Γ₁ Δ₀ n Ξ f gs refl)
⊗r+⇑N {Γ₀ = Γ₀} Γ₁ Δ₀ n Ξ (foc s q f) gs refl =
  foc s (isPosAt⊗⋆ tt (fmas Ξ)) (focr (just (_ , neg→negat n)) (⊗r+ Δ₀ Ξ (neg→isn't⊗ n) blurr gs refl) (unfoc n (⊸r⋆⇑ Γ₁ (foc s q f))) refl)

⊗r+⇑ : {S : Stp} {Γ : Cxt} (Δ₀ : Cxt) {B₀ A : Fma}
        (Ξ : List (Cxt × Fma))
        (f : S ∣ Γ ⇑ A)
        (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)) →
    ---------------------------------------------------------------------
        S ∣ Γ ++ Δ₀ ++ concat (cxts Ξ) ⇑ A ⊗⋆ (B₀ ∷ fmas Ξ)
⊗r+⇑ Δ₀ {A = ` X} Ξ f fs = ⊗r+⇑Q Δ₀ tt Ξ f fs
⊗r+⇑ Δ₀ {A = I} Ξ f fs = ⊗r+⇑Q Δ₀ tt Ξ f fs 
⊗r+⇑ Δ₀ {A = A' ⊗ B'} Ξ f fs = ⊗r+⇑Q Δ₀ tt Ξ f fs
⊗r+⇑ Δ₀ {A = A' ⊸ B'} Ξ f fs = ⊗r+⇑N [] Δ₀ tt Ξ f fs refl

⊗r⇑ : {S : Stp} {Γ Δ : Cxt} {A B : Fma}
       (f : S ∣ Γ ⇑ A)
       (g : ─ ∣ Δ ⇑ B) → 
    ---------------------------------------------------------------------
        S ∣ Γ ++ Δ ⇑ A ⊗ B
⊗r⇑ {Δ = Δ} f g = ⊗r+⇑ Δ [] f (g ∷ [])

-- -- (Iterated) ⊸-left

⊸l+⇑P : {S : Stp} (Γ₀ Δ₀ Δ₁ : Cxt) {Δ : Cxt} {A₀ P C : Fma}
         (p : isPos P)
         (Ξ : List (Cxt × Fma))
         (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ))
         (f : S ∣ Δ ⇑ C)
         (eq : Δ ≡ Δ₀ ++ Δ₁)
         (ℓ : L S Δ₀ P) →
    -----------------------------------------------------------------------------------------------
      just ((A₀ ∷ fmas Ξ) ⊸⋆ P) ∣ Γ₀ ++ concat (cxts Ξ) ++ Δ₁ ⇑ C
⊸l+⇑P Γ₀ Δ₀ Δ₁ p Ξ fs (⊸r f) refl ℓ = ⊸r (⊸l+⇑P Γ₀ Δ₀ (Δ₁ ∷ʳ _) p Ξ fs f refl ℓ)
⊸l+⇑P Γ₀ Δ₀ Δ₁ p Ξ fs (Il q f) eq ℓ = ⊸l+⇑P Γ₀ Δ₀ Δ₁ p Ξ fs f eq (Il-1 ℓ)
⊸l+⇑P Γ₀ Δ₀ Δ₁ p Ξ fs (⊗l q f) refl ℓ = ⊸l+⇑P Γ₀ (_ ∷ Δ₀) Δ₁ p Ξ fs f refl (⊗l-1 ℓ)
⊸l+⇑P Γ₀ Δ₀ Δ₁ {C = C} p Ξ fs (foc s q f) refl ℓ = 
  foc tt q (focl (pos→posat p) (⊸l+ Γ₀ Ξ (pos→posat p) fs blurl refl) (unfoc p (runLQ {Δ = Δ₁} q ℓ (foc s q f))) refl)

++lf : (Γ₀ : Cxt) {Γ : Cxt} {Q A₀ M : Fma} (Ξ : List (Cxt × Fma))
       (q : isPosAt Q)
       (lf : q ⇛lf just M ； Γ)
       (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)) →
       q ⇛lf just (A₀ ⊸ (fmas Ξ ⊸⋆ M)) ； (Γ₀ ++ concat (cxts Ξ) ++ Γ)
++lf Γ₀ Ξ q (⊸l+ Γ₁ {Δ} Ξ₁ q₁ fs lf refl) gs = 
  ⊸l+ Γ₀ (Ξ ++ (Γ₁ , _) ∷ Ξ₁) q₁ (gs ++All fs) lf (cong (λ x → Γ₀ ++ x ++ Δ) (sym (concat++ (cxts Ξ) (_ ∷ cxts Ξ₁))))
++lf Γ₀ Ξ q blurl gs = ⊸l+ Γ₀ Ξ q gs blurl refl

⊸l+⇑M : (Γ₀ : Cxt) {Δ : Cxt} {A₀ M C : Fma}
         (m : isNegAt M)
         (Ξ : List (Cxt × Fma))
         (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ))
         (f : just M ∣ Δ ⇑ C) → 
    -----------------------------------------------------------------------------------------------
      just ((A₀ ∷ fmas Ξ) ⊸⋆ M) ∣ Γ₀ ++ concat (cxts Ξ) ++ Δ ⇑ C
⊸l+⇓M : {b : Bool} (Γ₀ : Cxt) {Δ : Cxt} {A₀ M C : Fma}
         (m : isNegAt M)
         (Ξ : List (Cxt × Fma))
         (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ))
         (f : [ ∘ , b ] just M ∣ Δ ⇓ C) → 
    -----------------------------------------------------------------------------------------------
      [ ∘ , b ] just ((A₀ ∷ fmas Ξ) ⊸⋆ M) ∣ Γ₀ ++ concat (cxts Ξ) ++ Δ ⇓ C

⊸l+⇑M Γ₀ m Ξ fs (⊸r f) = ⊸r (⊸l+⇑M Γ₀ m Ξ fs f)
⊸l+⇑M Γ₀ m Ξ fs (foc s q f) = foc tt q (⊸l+⇓M Γ₀ m Ξ fs f)

⊸l+⇓M Γ₀ m Ξ fs (focl q lf f eq) = focl q (++lf Γ₀ Ξ q lf fs) f (cong (λ x → Γ₀ ++ concat (cxts Ξ) ++ x) eq)
⊸l+⇓M Γ₀ m Ξ fs (focr (just (M , m')) rf f eq) = focr (just (M , m')) rf (⊸l+⇓M Γ₀ m Ξ fs f) (cong (λ x → Γ₀ ++ concat (cxts Ξ) ++ x) eq)
⊸l+⇓M {∙} Γ₀ m Ξ fs (unfoc ok f) = unfoc ok (⊸l+⇑M Γ₀ m Ξ fs f)

⊸l+⇑ : (Γ₀ : Cxt) {Δ : Cxt} {A₀ B C : Fma}
         (Ξ : List (Cxt × Fma))
         (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ))
         (f : just B ∣ Δ ⇑ C) → 
    -----------------------------------------------------------------------
      just ((A₀ ∷ fmas Ξ) ⊸⋆ B) ∣ Γ₀ ++ concat (cxts Ξ) ++ Δ ⇑ C
⊸l+⇑ Γ₀ {B = ` X} Ξ fs f = ⊸l+⇑M Γ₀ tt Ξ fs f
⊸l+⇑ Γ₀ {B = I} Ξ fs f = ⊸l+⇑P Γ₀ [] _ tt Ξ fs f refl done
⊸l+⇑ Γ₀ {B = B ⊗ B₁} Ξ fs f = ⊸l+⇑P Γ₀ [] _ tt Ξ fs f refl done
⊸l+⇑ Γ₀ {B = B ⊸ B₁} Ξ fs f = ⊸l+⇑M Γ₀ tt Ξ fs f

⊸l⇑ : {Γ Δ : Cxt} {A B C : Fma}
      (f : ─ ∣ Γ ⇑ A)
      (g : just B ∣ Δ ⇑ C) → 
    -------------------------------
      just (A ⊸ B) ∣ Γ ++ Δ ⇑ C
⊸l⇑ {Γ} f g = ⊸l+⇑ Γ [] (f ∷ []) g

-- =========================================

-- The focusing function (in Theorem 1)

focus : ∀ {S Γ A} → S ∣ Γ ⊢ A → S ∣ Γ ⇑ A
focus ax = ax⇑
focus (pass f) = pass⇑ (focus f)
focus Ir = Ir⇑
focus (Il f) = Il⇑ (focus f)
focus (⊗r f g) = ⊗r⇑ (focus f) (focus g)
focus (⊗l f) = ⊗l⇑ (focus f)
focus (⊸r f) = ⊸r (focus f)
focus (⊸l f g) = ⊸l⇑ (focus f) (focus g)

focuss : ∀ {Ξ} → All (λ ΔB → ─ ∣ proj₁ ΔB ⊢ proj₂ ΔB) Ξ
  → All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ
focuss [] = []
focuss (f ∷ fs) = focus f ∷ focuss fs



-- =================================

-- Equivalence of multi-focused derivations

infixl 15 _•_

data _≗⇑_ : {S : Stp}{Γ : Cxt}{A : Fma} (f g : S ∣ Γ ⇑ A) → Set
data _≗⇓_ : {b c : Bool} {S : Stp}{Γ : Cxt}{A : Fma} (f g : [ b , c ] S ∣ Γ ⇓ A) → Set
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




