{-# OPTIONS --rewriting #-}

module MaxMultifocSeqCalc where

open import Data.List hiding (concat)
open import Data.List.Relation.Unary.All hiding (map)
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.Maybe hiding (map)
open import Data.Sum hiding (map)
open import Data.Product renaming (map to map×)
open import Data.Unit
open import Data.Empty
open import Data.Bool renaming (Bool to Tag; true to ∙; false to ∘)
open import Relation.Binary.PropositionalEquality hiding (_≗_)

open import Utilities
open import Formulae
open import SeqCalc

import MultifocSeqCalc as MF


-- Maximally multi-focused sequent calculus

-- =========================================

-- Tagged formulae, tagged contexts, tagged stoups

TFma : Set
TFma = Tag × Fma

TCxt : Set
TCxt = List TFma

TStp : Set
TStp = Tag × Stp

-- Operations on tagged formulae (contexts, stoups)

∘tfma : TFma → TFma
∘tfma (_ , A) = ∘ , A

∘tcxt : TCxt → TCxt
∘tcxt = map ∘tfma 

∙tfma : TFma → TFma
∙tfma (_ , A) = ∙ , A

∙tcxt : TCxt → TCxt
∙tcxt = map ∙tfma 

∙fma : Fma → TFma
∙fma A = ∙ , A

tag-fma : Tag → Fma → TFma
tag-fma l A = l , A

∙cxt : Cxt → TCxt
∙cxt = map ∙fma 

tag-cxt : Tag → Cxt → TCxt
tag-cxt t = map (tag-fma t)

∘fma : Fma → TFma
∘fma A = ∘ , A

∘cxt : Cxt → TCxt
∘cxt = map ∘fma 

untag-fma : TFma → Fma
untag-fma = proj₂

untag-cxt : TCxt → Cxt
untag-cxt = map untag-fma

untag-stp : TStp → Stp
untag-stp = proj₂

-- Side condition of right-focusing:
-- -- if the succedent formula is ∙ (red in the paper), then ∙ must
-- -- be in the context of the 2nd premise
rtag : Maybe (Σ Fma isNegAt) → TCxt → Tag → Set
rtag nothing _ _ = ⊤
rtag (just _) Γ ∘ = ⊤
rtag (just _) [] ∙ = ⊥
rtag (just s) ((∘ , A) ∷ Γ) ∙ = rtag (just s) Γ ∙
rtag (just _) ((∙ , A) ∷ Γ) ∙ = ⊤

-- Side condition of left-focusing:
-- -- if the stoup formula is ∙ (red in the paper), then ∙ must
-- -- be in the context of the 1st premise
ltag : TCxt → Tag → Set
ltag Γ ∘ = ⊤
ltag [] ∙ = ⊥
ltag ((∘ , A) ∷ Γ) ∙ = ltag Γ ∙
ltag ((∙ , A) ∷ Γ) ∙ = ⊤

ltag++ : ∀ Γ {A Δ} → ltag (Γ ++ (∙ , A) ∷ Δ) ∙
ltag++ [] = tt
ltag++ ((∘ , B) ∷ Γ) = ltag++ Γ
ltag++ ((∙ , B) ∷ Γ) = tt

end-rf? : (P : TStp → TCxt → Fma → Set) → TStp → TCxt → Maybe (Σ Fma isNegAt) → Set
end-rf? P S Γ (just (M , m)) = P S Γ M
end-rf? P S Γ ─ = proj₂ S ≡ nothing × Γ ≡ []

-- ================================

-- Inference rules

data _∣_⇑_ : TStp → TCxt → TFma → Set
data [_,_]_∣_⇓_ : Tag → Tag → TStp → TCxt → TFma → Set
data _⇛lf_∣_ {Q : Fma} (q : isPosAt Q) : Stp → Cxt → Set
data _⇛rf_；_  : Maybe (Σ Fma isNegAt) → Cxt → Fma → Set

data _∣_⇑_ where

  ⊸r : {l : Tag} {S : Stp} {Γ : TCxt} {A B : Fma} 
         (f : (l , S) ∣ Γ ∷ʳ (l , A) ⇑ (∘ , B)) →
       ---------------------------------
             (l , S) ∣ Γ ⇑ (∘ , A ⊸ B)

  Il : {r : Tag} {Γ : TCxt} {Q : Fma}
       (q : isPosAt Q)
       (f :  (∘ , ─) ∣ Γ ⇑ (r , Q)) →
    -------------------------
       (∘ , just I) ∣ Γ ⇑ (r , Q)

  ⊗l : {r : Tag} {Γ : TCxt} {A B Q : Fma}
       (q : isPosAt Q)
       (f : (∘ , just A) ∣ (r , B) ∷ Γ ⇑ (r , Q)) →
    -------------------------------------
         (∘ , just (A ⊗ B)) ∣ Γ ⇑ (r , Q) 

  foc : {l r : Tag} {S : Stp} {Γ : TCxt} {Q : Fma}
        (s : isIrr S) (q : isPosAt Q)
        (f : [ ∘ , ∘ ] (l , S) ∣ Γ ⇓ (r , Q)) → 
      ------------------------------------
               (l , S) ∣ Γ ⇑ (r , Q)

data [_,_]_∣_⇓_ where

  ax : {X : At} → [ ∙ , ∙ ] (∘ , just (` X)) ∣ [] ⇓ (∘ , ` X)

  focl : {l : Tag} {S : Stp} {Γ' : Cxt} {Γ Γ₀ Γ₁ : TCxt} {C : TFma} {Q : Fma}
         (q : isPosAt Q)
         (lf : q ⇛lf S ∣ Γ')
         (f : [ ∙ , ∘ ] (∘ , just Q) ∣ Γ₁ ⇓ C)          
         (eq : Γ ≡ Γ₀ ++ Γ₁)
         (eq' : Γ' ≡ untag-cxt Γ₀)
         (ξ : ltag Γ₀ l) → 
      ------------------------------------
          [ ∘ , ∘ ] (l , S) ∣ Γ ⇓ C

  focr : {b r : Tag} {S : TStp} {Γ' : Cxt} {Γ Γ₀ Γ₁ : TCxt} {C : Fma}
         (s : Maybe (Σ Fma isNegAt))
         (rf : s ⇛rf Γ' ； C) → 
         (f : end-rf? (λ T Δ A → [ b , ∙ ] T ∣ Δ ⇓ (∘ , A)) S Γ₀ s) → 
         (eq : Γ ≡ Γ₀ ++ Γ₁)
         (eq' : Γ' ≡ untag-cxt Γ₁)
         (ξ : rtag s Γ₁ r) → 
      ------------------------------------
           [ b , ∘ ] S ∣ Γ ⇓ (r , C)

  unfoc : {b b' l r : Tag} {S : Stp} {Γ : TCxt} {C : Fma}
          (ok : MF.UT b b' S C)
          (f : (not b , S) ∣ ∘tcxt Γ ⇑ (not b' , C)) →
      ------------------------------------
          [ b , b' ] (l , S) ∣ Γ ⇓ (r , C)

data _⇛lf_∣_ {Q} q' where

  pass : {Γ : Cxt} {A : Fma}
         (f : q' ⇛lf just A ∣ Γ) →
     ----------------------------------
         q' ⇛lf ─ ∣ (A ∷ Γ)

  ⊸l+ : (Γ₀ : Cxt) {Δ : Cxt} {A₀ Q : Fma}
         (Ξ : List (Cxt × Fma))
         (q : isPosAt Q)
         (fs : All (λ ΓA → (∘ , ─) ∣ ∘cxt (proj₁ ΓA) ⇑ (∘ , proj₂ ΓA)) ((Γ₀ , A₀) ∷ Ξ))
         (g : q' ⇛lf just Q ∣ Δ) →
      ----------------------------------------------------------
        q' ⇛lf just ((A₀ ∷ fmas Ξ) ⊸⋆ Q) ∣ (Γ₀ ++ concat (cxts Ξ) ++ Δ)

  blurl : q' ⇛lf just Q ∣ []

data _⇛rf_；_ where

  Ir : nothing ⇛rf [] ； I

  ⊗r+ : ∀ {Γ : Cxt} (Δ₀ : Cxt) {M B₀ : Fma} {s}
        (Ξ : List (Cxt × Fma))
        (m : isn't⊗ M)
        (f : s ⇛rf Γ ； M)
        (gs : All (λ ΔB → (∘ , ─) ∣ ∘cxt (proj₁ ΔB) ⇑ (∘ , proj₂ ΔB)) ((Δ₀ , B₀) ∷ Ξ)) →
      ------------------------------------
         s ⇛rf Γ ++ Δ₀ ++ concat (cxts Ξ) ； M ⊗⋆ (B₀ ∷ fmas Ξ)

  blurr : {M : Fma} {m : isNegAt M} → 
         just (M , m) ⇛rf [] ； M


subst⇑ : ∀ {S Γ Δ A} (f : S ∣ Γ ⇑ A) (eq : Γ ≡ Δ) → S ∣ Δ ⇑ A
subst⇑ f refl = f

subst⇓ : ∀ {b c S Γ Δ A} (f : [ b , c ] S ∣ Γ ⇓ A) (eq : Γ ≡ Δ) → [ b , c ] S ∣ Δ ⇓ A
subst⇓ f refl = f

-- ===================================

-- Embedding into multi-focused calculus (in Theorem 2)

untag⇑ : ∀ {S Γ A} → S ∣ Γ ⇑ A → untag-stp S MF.∣ untag-cxt Γ ⇑ untag-fma A
untag⇓ : ∀ {b c S Γ A} → [ b , c ] S ∣ Γ ⇓ A → MF.[ b , c ] untag-stp S ∣ untag-cxt Γ ⇓ untag-fma A
untags⇑ : ∀ {Ξ} → All (λ ΔB → (∘ , ─) ∣ ∘cxt (proj₁ ΔB) ⇑ ∘fma (proj₂ ΔB)) Ξ
  → All (λ ΔB → ─ MF.∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ
untag-lf : ∀ {S Γ Q} {q : isPosAt Q}→ q ⇛lf S ∣ Γ → q MF.⇛lf S ； Γ
untag-rf : ∀ {Γ A} {s : Maybe (Σ Fma isNegAt)}→ s ⇛rf Γ ； A → s MF.⇛rf Γ ； A

untag⇑ {Γ = Γ} (⊸r f) = MF.⊸r (untag⇑ {Γ = Γ ∷ʳ _} f)
untag⇑ (Il q f) = MF.Il q (untag⇑ f)
untag⇑ (⊗l q f) = MF.⊗l q (untag⇑ f)
untag⇑ (foc s q f) = MF.foc s q (untag⇓ f)

untags⇑ [] = []
untags⇑ {(Γ , A) ∷ Ξ} (f ∷ fs) = untag⇑ {Γ = ∘cxt Γ} f ∷ untags⇑ fs

untag⇓ ax = MF.ax
untag⇓ (focl q lf f refl refl ξ) = MF.focl q (untag-lf lf) (untag⇓ f) refl
untag⇓ (focr (just _) rf f refl refl ξ) = MF.focr _ (untag-rf rf) (untag⇓ f) refl
untag⇓ (focr ─ rf (refl , refl) refl refl ξ) = MF.focr _ (untag-rf rf) (refl , refl) refl
untag⇓ (unfoc {Γ = Γ} ok f) = MF.unfoc ok (untag⇑ {Γ = ∘tcxt Γ} f)

untag-lf (pass lf) = MF.pass (untag-lf lf)
untag-lf (⊸l+ Γ₀ Ξ q fs lf) = MF.⊸l+ Γ₀ Ξ q (untags⇑ fs) (untag-lf lf) refl
untag-lf blurl = MF.blurl

untag-rf Ir = MF.Ir
untag-rf (⊗r+ Δ₀ Ξ m rf gs) = MF.⊗r+ Δ₀ Ξ m (untag-rf rf) (untags⇑ gs) refl
untag-rf blurr = MF.blurr

-- ====================================

-- Some admissible rules

⊸r⋆⇑ : {l : Tag} {S : Stp} {Γ : TCxt} (Δ : Cxt) {A : Fma}
      (f : (l , S) ∣ Γ ++ tag-cxt l Δ ⇑ (∘ , A)) →
  --------------------------------------------
           (l , S) ∣ Γ ⇑ (∘ , Δ ⊸⋆ A)
⊸r⋆⇑ [] f = f
⊸r⋆⇑ (A' ∷ Δ) f = ⊸r (⊸r⋆⇑ Δ f) 


Il⇑ : {r : Tag} {Γ : TCxt} {C : Fma}
     (f :  (∘ , ─) ∣ Γ ⇑ (r , C)) →
  -------------------------
     (∘ , just I) ∣ Γ ⇑ (r , C)
Il⇑ (⊸r f) = ⊸r (Il⇑ f)
Il⇑ (foc s q f) = Il q (foc s q f)

⊗l⇑ : {r : Tag} {Γ : TCxt} {A B C : Fma}
     (f : (∘ , just A) ∣ (r , B) ∷ Γ ⇑ (r , C)) →
  -------------------------------------
       (∘ , just (A ⊗ B)) ∣ Γ ⇑ (r , C) 
⊗l⇑ (⊸r f) = ⊸r (⊗l⇑ f)
⊗l⇑ (Il q f) = ⊗l q (Il q f)
⊗l⇑ (⊗l q f) = ⊗l q (⊗l⇑ f)
⊗l⇑ (foc s q f) = ⊗l q (foc s q f)

runLQ : ∀ {r S Γ Δ A Q} (q : isPosAt Q) → MF.L S Γ A
  → (∘ , S) ∣ tag-cxt r Γ ++ Δ ⇑ (r , Q)
  → (∘ , just A) ∣ Δ ⇑ (r , Q)
runLQ q MF.done f = f
runLQ q (MF.Il-1 ℓ) f = runLQ q ℓ (Il q f)
runLQ q (MF.⊗l-1 ℓ) f = runLQ q ℓ (⊗l q f)

runL : ∀ {r S Γ Δ A C} → MF.L S Γ A
  → (∘ , S) ∣ tag-cxt r Γ ++ Δ ⇑ (r , C)
  → (∘ , just A) ∣ Δ ⇑ (r , C)
runL MF.done f = f
runL (MF.Il-1 ℓ) f = runL ℓ (Il⇑ f)
runL (MF.⊗l-1 ℓ) f = runL ℓ (⊗l⇑ f)

-- ========================================

-- Some lemmata

-- All ∙tags can be removed from context

untag-seq : {S : Stp} {Γ : TCxt} {A : Fma}
        (f : (∘ , S) ∣ Γ ⇑ (∘ , A)) →
  --------------------------------------
           (∘ , S) ∣ ∘tcxt Γ ⇑ (∘ , A)
untag-seq-f : {b b' : Tag} {S : Stp} {Γ : TCxt} {A : Fma}
        (f : [ b , b' ] (∘ , S) ∣ Γ ⇓ (∘ , A)) →
  --------------------------------------
          [ b , b' ] (∘ , S) ∣ ∘tcxt Γ ⇓ (∘ , A)

untag-seq {Γ = Γ} (⊸r f) = ⊸r (untag-seq {Γ = Γ ∷ʳ _} f)
untag-seq (Il q f) = Il q (untag-seq f)
untag-seq (⊗l q f) = ⊗l q (untag-seq f)
untag-seq (foc s q f) = foc s q (untag-seq-f f)

untag-seq-f ax = ax
untag-seq-f (focl {Γ₀ = Γ₀}{Γ₁} q lf f refl eq' ξ) =
  focl {Γ₀ = ∘tcxt Γ₀} {∘tcxt Γ₁} q lf (untag-seq-f f) refl eq' ξ
untag-seq-f (focr {Γ₀ = Γ₀} {Γ₁} (just x) rf f refl eq' ξ) =
  focr {Γ₀ = ∘tcxt Γ₀} {∘tcxt Γ₁} _ rf (untag-seq-f f) refl eq' ξ
untag-seq-f (focr {Γ₀ = Γ₀} {Γ₁} ─ rf (refl , refl) refl eq' ξ) =
  focr {Γ₀ = ∘tcxt Γ₀}{∘tcxt Γ₁} nothing rf (refl , refl) refl eq' ξ
untag-seq-f (unfoc ok f) = unfoc ok f

-- A derivation of a sequent with ∙tagged stoup is turned in a
-- derivation of the same sequent with ∘tagged stoup (and all
-- ∘tagged context)

l∙→∘⇑ : ∀ {S Γ C} → (∙ , S) ∣ Γ ⇑ (∘ , C) → (∘ , S) ∣ ∘tcxt Γ ⇑ (∘ , C)
l∙→∘⇑ (⊸r {Γ = Γ} f) = ⊸r {Γ = ∘tcxt Γ} (l∙→∘⇑ {Γ = Γ ∷ʳ _} f)
l∙→∘⇑ (foc s q (focl {Γ₀ = Γ₀}{Γ₁} q₁ lf f refl eq' ξ)) =
  foc s q (focl {Γ₀ = ∘tcxt Γ₀}{∘tcxt Γ₁} q₁ lf (untag-seq-f f) refl eq' tt)
l∙→∘⇑ (foc s q (focr {Γ₀ = Γ₀}{Γ₁} (just x) rf (unfoc ok f) refl eq' ξ)) =
  foc s q (focr {Γ₀ = ∘tcxt Γ₀} {∘tcxt Γ₁} (just x) rf (unfoc ok f) refl eq' tt)
l∙→∘⇑ (foc s q (focr {Γ₀ = Γ₀}{Γ₁} nothing rf (refl , refl) refl eq' ξ)) =
  foc s q (focr {Γ₀ = ∘tcxt Γ₀} {∘tcxt Γ₁} nothing rf (refl , refl) refl eq' tt)

-- A derivation of a sequent with ∙tagged succedent is turned in a
-- derivation of the same sequent with ∘tagged succedent (and all
-- ∘tagged context)

r∙→∘⇑ : ∀ {S Γ C} → (∘ , S) ∣ Γ ⇑ (∙ , C) → (∘ , S) ∣ ∘tcxt Γ ⇑ (∘ , C)
r∙→∘⇑ (Il q f) = Il q (r∙→∘⇑ f)
r∙→∘⇑ (⊗l q f) = ⊗l q (r∙→∘⇑ f)
r∙→∘⇑ (foc s q (focl {Γ₀ = Γ₀} q₁ lf (focr {Γ₀ = Γ₁} {Γ₂} (just x) rf f refl refl ξ₁) refl refl ξ)) = 
  foc s q (focl {Γ₀ = ∘tcxt Γ₀} {∘tcxt (Γ₁ ++ Γ₂)} _ lf (focr {Γ₀ = ∘tcxt Γ₁} {∘tcxt Γ₂} _ rf (untag-seq-f f) refl refl tt) refl refl tt)
r∙→∘⇑ (foc s q (focl {Γ₀ = Γ₀}{Γ₁} q₁ lf (unfoc ok f) refl refl ξ)) =
  foc s q (focl {Γ₀ = ∘tcxt Γ₀} {∘tcxt Γ₁} _ lf (unfoc ok f) refl refl tt)
r∙→∘⇑ (foc s q (focr {Γ₀ = Γ₀}{Γ₁} (just _) rf f refl refl ξ)) =
  foc s q (focr {Γ₀ = ∘tcxt Γ₀}{∘tcxt Γ₁} (just _) rf (untag-seq-f f) refl refl tt)
r∙→∘⇑ (foc s q (focr {Γ₀ = Γ₀}{Γ₁} nothing rf (refl , refl) refl refl ξ)) =
  foc s q (focr {Γ₀ = ∘tcxt Γ₀}{∘tcxt Γ₁} nothing rf (refl , refl) refl refl tt)

-- ====================================================

-- Admissibility of left-focusing with both premise and conclusion in
-- invertible phase.

only-lf-f-at : {S : Stp} {Δ₀ : Cxt} (Δ₁ : TCxt) {C X : Fma}
               (s : isIrr S) (x : isAt X)
               (lf : at→posat x ⇛lf S ∣ Δ₀) 
               (f : [ ∘ , ∘ ] (∘ , just X) ∣ Δ₁ ⇓ (∘ , C)) → 
      ------------------------------------
           [ ∘ , ∘ ] (∘ , S) ∣ ∘cxt Δ₀ ++ Δ₁ ⇓ (∘ , C)
only-lf-f-at Δ₁ s x lf (focl {Γ₀ = []} q₁ blurl f refl refl ξ) = focl (at→posat x) lf f refl refl tt
only-lf-f-at Δ₁ s x lf (focr {Γ₀ = Γ₀} (just (M , m)) rf (unfoc ok f) eq refl ξ) =
  focl (at→posat x) lf (focr (just (M , m)) rf (unfoc (inj₂ ok) (l∙→∘⇑ {Γ = ∘tcxt Γ₀} f)) eq refl ξ) refl refl tt

only-lf⇑-at : {S : Stp} {Δ₀ : Cxt} (Δ₁ : TCxt) {C X : Fma}
               (s : isIrr S) (x : isAt X)
               (lf : at→posat x ⇛lf S ∣ Δ₀) 
               (f : (∘ , just X) ∣ Δ₁ ⇑ (∘ , C)) → 
      ------------------------------------
           (∘ , S) ∣ ∘cxt Δ₀ ++ Δ₁ ⇑ (∘ , C)
only-lf⇑-at Δ₁ s x lf (⊸r f) = ⊸r (only-lf⇑-at (Δ₁ ∷ʳ _) s x lf f)
only-lf⇑-at Δ₁ s x lf (foc s₁ q f) = foc s q (only-lf-f-at Δ₁ s x lf f)


only-lf⇑ : {S : Stp} {Δ₀ : Cxt} (Δ₁ : TCxt) {C Q : Fma}
               (s : isIrr S) (q : isPosAt Q)
               (lf : q ⇛lf S ∣ Δ₀) 
               (f : (∘ , just Q) ∣ Δ₁ ⇑ (∘ , C)) → 
      ------------------------------------
           (∘ , S) ∣ ∘cxt Δ₀ ++ Δ₁ ⇑ (∘ , C)

only-lf⇑P : {S S' : Stp} {Δ : TCxt} {Δ₀ : Cxt} (Δ₁ : TCxt) {Γ : Cxt} {C P : Fma}
            (s : isIrr S) (p : isPos P)
            (lf : pos→posat p ⇛lf S ∣ Δ₀) 
            (f : (∘ , S') ∣ Δ ⇑ (∘ , C)) → 
            (eq : Δ ≡ ∘cxt Γ ++ Δ₁)
            (ℓ : MF.L S' Γ P) →
      ------------------------------------
           (∘ , S) ∣ ∘cxt Δ₀ ++ Δ₁ ⇑ (∘ , C)

only-lf-fP : {S S' : Stp} {Δ : TCxt} {Δ₀ : Cxt} (Δ₁ : TCxt) {Γ : Cxt} {Q P : Fma}
            (s' : isIrr S') (p : isPos P) (q : isPosAt Q)
            (lf : pos→posat p ⇛lf S ∣ Δ₀) 
            (f : [ ∘ , ∘ ] (∘ , S') ∣ Δ ⇓ (∘ , Q)) → 
            (eq : Δ ≡ ∘cxt Γ ++ Δ₁)
            (ℓ : MF.L S' Γ P) →
      ------------------------------------
           [ ∘ , ∘ ] (∘ , S) ∣ ∘cxt Δ₀ ++ Δ₁ ⇓ (∘ , Q)


only-lf⇑ Δ₁ {Q = ` X} s p lf f = only-lf⇑-at Δ₁ s p lf f
only-lf⇑ Δ₁ {Q = I} s p lf f = only-lf⇑P Δ₁ s p lf f refl MF.done
only-lf⇑ Δ₁ {Q = Q ⊗ Q₁} s p lf f = only-lf⇑P Δ₁ s p lf f refl MF.done

only-lf⇑P Δ₁ s p lf (⊸r f) refl ℓ = ⊸r (only-lf⇑P (Δ₁ ∷ʳ _) s p lf f refl ℓ)
only-lf⇑P Δ₁ s p lf (Il q₁ f) eq ℓ = only-lf⇑P Δ₁ s p lf f eq (MF.Il-1 ℓ)
only-lf⇑P Δ₁ s p lf (⊗l q₁ f) refl ℓ = only-lf⇑P Δ₁ s p lf f refl (MF.⊗l-1 ℓ)
only-lf⇑P Δ₁ s p lf (foc s' q₁ f) eq ℓ = foc s q₁ (only-lf-fP Δ₁ s' p q₁ lf f eq ℓ)

only-lf-fP {Δ₀ = Δ₀} Δ₁ {Γ} s' p q lf (focl {Γ₀ = Γ₀} {Γ₁} q₂ lf₁ (focr (just (.(` _) , snd)) rf ax refl refl ξ) refl refl ξ') eq ℓ with ++?-alt (∘cxt Γ) Γ₀ Δ₁ Γ₁ eq
... | inj₁ (Ω , refl , refl) =
  focl {Γ₀ = ∘cxt Δ₀}{Δ₁} (pos→posat p) lf
       (focr {Γ₀ = Ω} {Γ₁} (just _) rf (unfoc (inj₁ p) (runLQ {Δ = ∘tcxt Ω} tt ℓ (foc s' tt (focl {Γ₁ = []} tt lf₁ (focr (just _) blurr ax refl refl tt) refl refl tt)))) refl refl tt)
       refl refl tt
... | inj₂ (A , Ω , eq' , refl) with split-map ∘fma Γ Γ₀ (A ∷ Ω) eq'
... | (Γ₀' , _ ∷ Ω' , refl , refl , refl) =
  focl (pos→posat p) lf
       (unfoc p (runLQ {Δ = ∘tcxt Δ₁} q ℓ (foc s' q (focl {Γ₀ = ∙cxt Γ₀'} {_ ∷ ∙cxt Ω' ++ ∘tcxt Δ₁} tt lf₁ (focr {Γ₀ = []} _ rf ax refl refl tt) refl refl tt))))
       refl refl tt
only-lf-fP {Δ₀ = Δ₀} Δ₁ {Γ} s' p q lf (focl {Γ₀ = Γ₂} q₂ lf₁ (focr {Γ₀ = Γ₀} {Γ₁} (just (M , m)) rf (unfoc ok f) refl refl ξ) refl refl ξ') eq ℓ with ++?-alt (∘cxt Γ) (Γ₂ ++ Γ₀) Δ₁ Γ₁ eq
... | inj₁ (Ω , eq' , refl) with ++?-alt (∘cxt Γ) Γ₂ Ω Γ₀ eq'
... | inj₁ (Λ , refl , refl) =
  focl {Γ₀ = ∘cxt Δ₀} {Δ₁} (pos→posat p) lf
       (focr {Γ₀ = Λ ++ Γ₀} {Γ₁} _ rf (unfoc (inj₁ p) (runL {Δ = ∘tcxt (Λ ++ Γ₀)} ℓ (only-lf⇑ {Δ₀ = Γ ++ untag-cxt Λ} (∘tcxt Γ₀) s' q₂ lf₁ f))) refl refl tt)
       refl refl tt
... | inj₂ (A' , Λ , eq'' , refl) with split-map ∘fma Γ Γ₂ (_ ∷ Λ) eq''
... | (Γ₂' , _ ∷ Λ' , refl , refl , refl) =
  focl {Γ₀ = ∘cxt Δ₀} {Ω ++ Γ₁} (pos→posat p) lf
       (focr {Γ₀ = Ω} {Γ₁} (just (M , m)) rf (unfoc (inj₁ p) (runL {Δ = ∘tcxt Ω} ℓ (only-lf⇑ {Δ₀ = Γ₂'} (_ ∷ ∘cxt Λ' ++ ∘tcxt Ω) s' q₂ lf₁ f))) refl refl tt)
       refl refl tt
only-lf-fP {Δ₀ = Δ₀} Δ₁ {Γ} s' p q lf (focl {Γ₀ = Γ₂} q₂ lf₁ (focr {Γ₀ = Γ₀} (just x) rf (unfoc ok f) refl refl ξ) refl refl ξ') eq ℓ | inj₂ (A , Ω , eq' , refl)
  with split-map ∘fma Γ Γ₂ (Γ₀ ++ _ ∷ Ω) eq'
... | (Γ₂' , Λ , refl , eq'' , refl) with split-map ∘fma Λ Γ₀ (_ ∷ Ω) eq''
... | (Γ₀' , _ ∷ Ω' , refl , refl , refl) =
  focl {Γ₀ = ∘cxt Δ₀} {Δ₁} (pos→posat p) lf
       (unfoc p (runLQ {Δ = ∘tcxt Δ₁} q ℓ
              (foc s' q (focl {Γ₀ = ∙cxt Γ₂'} {∙cxt Γ₀' ++ _ ∷ ∙cxt Ω' ++ ∘tcxt Δ₁} q₂ lf₁ (focr {Γ₀ = ∙cxt Γ₀'} {_ ∷ ∙cxt Ω' ++ ∘tcxt Δ₁} _ rf (unfoc ok f) refl refl tt) refl refl tt))))
       refl refl tt
only-lf-fP {Δ₀ = Δ₀} Δ₁ {Γ} s' p q lf (focl {Γ₀ = Γ₀} {Γ₁} q₂ lf₁ (unfoc ok f) refl refl ξ) eq ℓ with ++?-alt (∘cxt Γ) Γ₀ Δ₁ Γ₁ eq
... | inj₁ (Ω , refl , refl) =
  focl {Γ₀ = ∘cxt Δ₀} {Δ₁} (pos→posat p) lf (unfoc p (runLQ {Δ = ∘tcxt Δ₁} q ℓ (foc s' q (focl {Γ₀ = ∙cxt Γ ++ ∘tcxt Ω} {∘tcxt Γ₁} q₂ lf₁ (unfoc ok f) refl refl tt)))) refl refl tt
... | inj₂ (A , Ω , eq' , refl) with split-map ∘fma Γ Γ₀ (A ∷ Ω) eq'
... | (Γ₀' , _ ∷ Ω' , refl , refl , refl) =
  focl {Γ₀ = ∘cxt Δ₀} {Δ₁} (pos→posat p) lf (unfoc p (runLQ {Δ = ∘tcxt Δ₁} q ℓ (foc s' q (focl {Γ₀ = ∙cxt Γ₀'} {_ ∷ ∙cxt Ω' ++ ∘tcxt Δ₁} q₂ lf₁ (unfoc ok f) refl refl tt)))) refl refl tt
only-lf-fP {Δ₀ = Δ₀} Δ₁ {Γ} s' p q lf (focr {Γ₀ = Γ₀} {Γ₁} (just (M , m)) rf (unfoc ok f) refl refl ξ) eq ℓ with ++?-alt (∘cxt Γ) Γ₀ Δ₁ Γ₁ eq
... | inj₁ (Ω , refl , refl) =
  focl {Γ₀ = ∘cxt Δ₀} {Ω ++ Γ₁} (pos→posat p) lf (focr {Γ₀ = Ω} {Γ₁} (just (M , m)) rf (unfoc (inj₁ p) (runL {Δ = ∘tcxt Ω} ℓ (l∙→∘⇑ {Γ = ∘cxt Γ ++ ∘tcxt Ω} f))) refl refl ξ) refl refl tt
... | inj₂ (A , Ω , eq' , refl) with split-map ∘fma Γ Γ₀ (A ∷ Ω) eq'
... | (Γ₀' , _ ∷ Ω' , refl , refl , refl) =
  focl {Γ₀ = ∘cxt Δ₀} {Δ₁} (pos→posat p) lf (unfoc p (runLQ {Δ = ∘tcxt Δ₁} q ℓ (foc s' q (focr {Γ₀ = ∙cxt Γ₀'} {_ ∷ ∙cxt Ω' ++ ∘tcxt Δ₁} (just (M , m)) rf (unfoc ok f) refl refl ξ)))) refl refl tt
only-lf-fP {Δ₀ = Δ₀} Δ₁ {Γ} s' p q lf (focr ─ rf (refl , refl) refl refl ξ) refl ℓ =
  focl {Γ₀ = ∘cxt Δ₀} {Δ₁} (pos→posat p) lf (unfoc p (runLQ {Δ = ∘tcxt Δ₁} q ℓ (foc tt q (focr {Γ₀ = []}{∙cxt Γ ++ ∘tcxt Δ₁} nothing rf (refl , refl) refl refl tt)))) refl refl tt

-- Admissibility of right-focusing with both premise and conclusion in
-- invertible phase.

only-rf-f-at : {S : Stp} (Δ₀ : TCxt) {Δ₁ : Cxt} {X Q : Fma}
               (x : isAt X) (q : isPosAt Q)
               (rf : just (X , at→negat x) ⇛rf Δ₁ ； Q) 
               (f : [ ∘ , ∘ ] (∘ , S) ∣ Δ₀ ⇓ (∘ , X)) → 
              ------------------------------------
               [ ∘ , ∘ ] (∘ , S) ∣ Δ₀ ++ ∘cxt Δ₁ ⇓ (∘ , Q)
only-rf-f-at _ x q rf (focl {Γ₀ = Γ₀} q₁ lf (focr (just (M , m)) (⊗r+ Δ₀ Ξ m₁ rf₁ gs) f refl eq' ξ₁) refl refl ξ) = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))
only-rf-f-at _ {Δ₁} x q rf (focl {Γ₀ = Γ₀} q₁ lf (focr {Γ₀ = Γ₁} {[]} (just (M , m)) blurr f refl refl ξ₁) refl refl ξ) =
  focl {Γ₀ = Γ₀} {Γ₁ ++ ∘cxt Δ₁} _ lf (focr {Γ₀ = Γ₁} {∘cxt Δ₁} _ rf f refl refl tt) refl refl tt
only-rf-f-at Δ₀ {Δ₁} x q rf (focl {Γ₀ = Γ₀}{Γ₁} q₁ lf (unfoc ok f) refl refl ξ) =
  focl {Γ₀ = Γ₀} {Γ₁ ++ ∘cxt Δ₁} _ lf (focr {Γ₀ = Γ₁} {∘cxt Δ₁} _ rf (unfoc (inj₁ ok) (r∙→∘⇑ {Γ = ∘tcxt Γ₁} f)) refl refl tt) refl refl tt
only-rf-f-at ._ x q rf (focr (just x₁) (⊗r+ Δ₀ Ξ m rf₁ gs) f refl eq ξ) = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))
only-rf-f-at .Γ₀ {Δ₁} x q rf (focr {Γ₀ = Γ₀} {[]} (just .(_ , _)) blurr f refl refl ξ) =
  focr {Γ₀ = Γ₀} {∘cxt Δ₁} _ rf f refl refl tt
only-rf-f-at ._ x q rf (focr ─ (⊗r+ Δ₀ Ξ m rf₁ gs) (refl , refl) refl eq ξ) = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))

only-rf⇑-at : {S : Stp} (Δ₀ : TCxt) {Δ₁ : Cxt} {X Q : Fma}
               (x : isAt X) (q : isPosAt Q)
               (rf : just (X , at→negat x) ⇛rf Δ₁ ； Q) 
               (f : (∘ , S) ∣ Δ₀ ⇑ (∘ , X)) → 
              ------------------------------------
               (∘ , S) ∣ Δ₀ ++ ∘cxt Δ₁ ⇑ (∘ , Q)
only-rf⇑-at Δ₀ x q rf (Il q₁ f) = Il q (only-rf⇑-at Δ₀ x q rf f)
only-rf⇑-at Δ₀ x q rf (⊗l q₁ f) = ⊗l q (only-rf⇑-at (_ ∷ Δ₀) x q rf f)
only-rf⇑-at Δ₀ x q rf (foc s q₁ f) = foc s q (only-rf-f-at Δ₀ x q rf f)

only-rf⇑ : {S : Stp} (Δ₀ : TCxt) {Δ₁ : Cxt} {M Q : Fma}
              (m : isNegAt M) (q : isPosAt Q)
              (rf : just (M , m) ⇛rf Δ₁ ； Q) 
               (f : (∘ , S) ∣ Δ₀ ⇑ (∘ , M)) → 
              ------------------------------------
               (∘ , S) ∣ Δ₀ ++ ∘cxt Δ₁ ⇑ (∘ , Q)

only-rf⇑N : {S : Stp} {Δ : TCxt} (Δ₀ : TCxt) {Δ₁ : Cxt} (Γ : Cxt) {B Q : Fma}
               (n : isNeg (Γ ⊸⋆ B)) (q : isPosAt Q)
               (rf : just (Γ ⊸⋆ B , neg→negat n) ⇛rf Δ₁ ； Q) 
               (f : (∘ , S) ∣ Δ ⇑ (∘ , B))
               (eq : Δ ≡ Δ₀ ++ ∘cxt Γ) → 
              ------------------------------------
               (∘ , S) ∣ Δ₀ ++ ∘cxt Δ₁ ⇑ (∘ , Q)

only-rf-fN : {S : Stp} {Δ : TCxt} (Δ₀ : TCxt) {Δ₁ : Cxt} (Γ : Cxt) {Q Q' : Fma}
               (s : isIrr S) (n : isNeg (Γ ⊸⋆ Q')) (q : isPosAt Q) (q' : isPosAt Q')
               (rf : just (Γ ⊸⋆ Q' , neg→negat n) ⇛rf Δ₁ ； Q) 
               (f : [ ∘ , ∘ ] (∘ , S) ∣ Δ ⇓ (∘ , Q'))
               (eq : Δ ≡ Δ₀ ++ ∘cxt Γ) → 
              ------------------------------------
               [ ∘ , ∘ ] (∘ , S) ∣ Δ₀ ++ ∘cxt Δ₁ ⇓ (∘ , Q)

only-rf⇑ Δ₀ {M = ` X} m q rf f = only-rf⇑-at Δ₀ m q rf f
only-rf⇑ Δ₀ {M = A ⊸ B} m q rf f = only-rf⇑N Δ₀ [] tt q rf f refl

only-rf⇑N Δ₀ Γ n q rf (⊸r f) refl = only-rf⇑N Δ₀ (Γ ∷ʳ _) n q rf f refl 
only-rf⇑N Δ₀ Γ n q rf (Il _ f) eq = Il q (only-rf⇑N Δ₀ Γ n q rf f eq)
only-rf⇑N Δ₀ Γ n q rf (⊗l _ f) refl = ⊗l q (only-rf⇑N (_ ∷ Δ₀) Γ n q rf f refl)
only-rf⇑N Δ₀ Γ n q rf (foc s q' f) eq = foc s q (only-rf-fN Δ₀ Γ s n q q' rf f eq)

only-rf-fN Δ₀ {Δ₁} Γ s n q q' rf (focl {Γ₀ = Γ₀} {Γ₁} q₁ lf (focr (just (._ , snd)) rf₁ ax refl refl ξ₁) refl refl ξ) eq with ++? _ Γ₀ (∘cxt Γ) Γ₁ eq
... | inj₁ (Λ , refl , refl) =
  focl {Γ₀ = Γ₀} {Λ ++ ∘cxt Δ₁} q₁ lf
       (focr {Γ₀ = Λ} {∘cxt Δ₁} (just _) rf (unfoc (inj₂ n) (⊸r⋆⇑ Γ (foc tt q' (focl {Γ₀ = []} _ blurl (focr {Γ₀ = []} {∘tcxt Λ ++ ∘cxt Γ} _ rf₁ ax refl refl tt) refl refl tt)))) refl refl tt)
       refl refl tt
... | inj₂ (A , Λ , refl , eq') with split-map ∘fma Γ (_ ∷ Λ) Γ₁ eq'
... | _ ∷ Λ' , Γ₁' , refl , refl , refl =
  focr {Γ₀ = _} {∘cxt Δ₁} _ rf
       (unfoc tt (⊸r⋆⇑ (_ ∷ Λ' ++ Γ₁') (foc s q' (focl {Γ₀ = ∘tcxt _ ++ _ ∷ ∙cxt Λ'} {∙cxt Γ₁'} _ lf (focr {Γ₀ = []} {∙cxt Γ₁'} _ rf₁ ax refl refl tt) refl refl (ltag++ (∘tcxt Δ₀))))))
       refl refl tt
only-rf-fN _ {Δ₁} Γ s n q q' rf (focl {Γ₀ = Γ₀} q₁ lf (focr {Γ₀ = Γ₁} {Γ₂} (just (M , m)) rf₁ (unfoc ok f) refl refl ξ₁) refl refl ξ) eq with ++? _ Γ₀ (∘cxt Γ) (Γ₁ ++ Γ₂) eq
... | inj₁ (Λ , eq' , refl) with ++? Λ Γ₁ (∘cxt Γ) Γ₂ eq'
... | inj₁ (Λ' , refl , refl) =
  focl {Γ₀ = Γ₀} {Γ₁ ++ Λ' ++ ∘cxt Δ₁} q₁ lf (focr {Γ₀ = Γ₁ ++ Λ'} {∘cxt Δ₁} (just _) rf (unfoc (inj₂ n) (⊸r⋆⇑ Γ (only-rf⇑ _ m q' rf₁ f))) refl refl tt) refl refl tt
... | inj₂ (A' , Λ' , refl , eq'') with split-map ∘fma Γ (_ ∷ Λ') Γ₂ eq''
... | _ ∷ Λ'' , Γ₂' , refl , refl , refl =
  focl {Γ₀ = Γ₀} {Λ ++ ∘cxt Δ₁} q₁ lf (focr {Γ₀ = Λ} {∘cxt Δ₁} (just _) rf (unfoc (inj₂ tt) (⊸r⋆⇑ (_ ∷ Λ'' ++ Γ₂') (only-rf⇑ _ m q' rf₁ f))) refl refl tt) refl refl tt
only-rf-fN Δ₀ {Δ₁} Γ s n q q' rf (focl q₁ lf (focr {Γ₀ = Γ₁} {Γ₂} (just x) rf₁ (unfoc ok f) refl refl ξ₁) refl refl ξ) eq | inj₂ (A , Λ , refl , eq') with split-map ∘fma Γ (_ ∷ Λ) (Γ₁ ++ Γ₂) eq'
... | _ ∷ Λ' , Ω , refl , eq'' , refl with split-map ∘fma Ω Γ₁ Γ₂ eq''
... | Γ₁' , Γ₂' , refl , refl , refl = 
  focr {Γ₀ = _}{∘cxt Δ₁} _ rf
       (unfoc n (⊸r⋆⇑ Γ (foc s q' (focl {Γ₀ = ∘tcxt _ ++ _ ∷ ∙cxt Λ'}{∙cxt (Γ₁' ++ Γ₂')} _ lf (focr {Γ₀ = ∙cxt Γ₁'}{∙cxt Γ₂'} _ rf₁ (unfoc ok f) refl refl tt) refl refl (ltag++ (∘tcxt Δ₀))))))
       refl refl tt
only-rf-fN Δ₀ {Δ₁} Γ s n q q' rf (focl {Γ₀ = Γ₀} {Γ₁} q₁ lf (unfoc ok f) refl refl ξ) eq with ++? _ Γ₀ (∘cxt Γ) Γ₁ eq
... | inj₁ (Λ , refl , refl) =
  focl {Γ₀ = Γ₀} {Λ ++ ∘cxt Δ₁} q₁ lf (focr {Γ₀ = Λ}{∘cxt Δ₁} _ rf (unfoc (inj₁ ok) (⊸r⋆⇑ Γ (r∙→∘⇑ {Γ = ∘tcxt Λ ++ ∘cxt Γ} f))) refl refl tt) refl refl tt
... | inj₂ (A , Λ , refl , eq') with split-map ∘fma Γ (_ ∷ Λ) Γ₁ eq'
... | _ ∷ Λ' , Γ₁' , refl , refl , refl =
  focr {Γ₀ = _}{∘cxt Δ₁} _ rf (unfoc tt (⊸r⋆⇑ (_ ∷ Λ' ++ Γ₁') (foc s q' (focl {Γ₀ = ∘tcxt _ ++ _ ∷ ∙cxt Λ'}{∙cxt Γ₁'} _ lf (unfoc ok f) refl refl (ltag++ (∘tcxt Δ₀)))))) refl refl tt
only-rf-fN _ {Δ₁} Γ s n q q' rf (focr {Γ₀ = Γ₀} {Γ₁} (just (M , m)) rf₁ (unfoc ok f) refl refl ξ) eq with ++? _ Γ₀ (∘cxt Γ) Γ₁ eq
... | inj₁ (Λ , refl , refl) =
  focr {Γ₀ = Γ₀ ++ Λ} {∘cxt Δ₁} _ rf (unfoc n (⊸r⋆⇑ Γ (foc s q' (focr {Γ₀ = ∘tcxt Γ₀}{∘tcxt Λ ++ ∙cxt Γ} _ rf₁ (unfoc ok f) refl refl tt)))) refl refl tt
... | inj₂ (A , Λ , refl , eq') with split-map ∘fma Γ (_ ∷ Λ) Γ₁ eq'
... | _ ∷ Λ' , Γ₁' , refl , refl , refl =
  focr {Γ₀ = _}{∘cxt Δ₁} _ rf (unfoc tt (⊸r⋆⇑ (_ ∷ Λ' ++ Γ₁') (foc s q' (focr {Γ₀ = ∘tcxt _ ++ _ ∷ ∙cxt Λ'}{∙cxt Γ₁'} _ rf₁ (unfoc ok f) refl refl tt)))) refl refl tt
only-rf-fN _ {Δ₁} Γ s n q q' rf (focr ─ rf₁ (refl , refl) refl refl ξ) refl =
  focr {Γ₀ = _}{∘cxt Δ₁} _ rf (unfoc n (⊸r⋆⇑ Γ (foc s q' ((focr {Γ₀ = []}{∘tcxt _ ++ ∙cxt Γ} nothing rf₁ (refl , refl) refl refl tt))))) refl refl tt

-- ====================================================

-- The maximal multi-focusing function (in Theorem 2)

max : ∀ {S Γ A} → S MF.∣ Γ ⇑ A → (∘ , S) ∣ ∘cxt Γ ⇑ (∘ , A)
maxs : ∀ {Ξ} → All (λ ΔB → ─ MF.∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ
  → All (λ ΔB → (∘ , ─) ∣ ∘cxt (proj₁ ΔB) ⇑ (∘ , proj₂ ΔB)) Ξ
max-lf : ∀ {S Γ Q} {q : isPosAt Q}→ q MF.⇛lf S ； Γ → q ⇛lf S ∣ Γ
max-rf : ∀ {Γ A} {s : Maybe (Σ Fma isNegAt)}→ s MF.⇛rf Γ ； A → s ⇛rf Γ ； A

max {Γ = Γ} (MF.⊸r f) = ⊸r (max {Γ = Γ ∷ʳ _} f)
max (MF.Il q f) = Il q (max f)
max (MF.⊗l q f) = ⊗l q (max f)

-- easy cases:

-- -- ax
--max (MF.foc s q MF.ax) = foc tt tt (focl tt blurl (focr (just _) blurr ax refl refl tt) refl refl tt)
-- -- focL + ax
--max (MF.foc s q (MF.focl {Γ₀ = Γ₀} {.[]} q₁ lf MF.ax refl)) =
--  foc s tt (only-lf-f-at [] s tt (max-lf lf) (focl tt blurl (focr (just _) blurr ax refl refl tt) refl refl tt))
-- -- focR + ax  
--max (MF.foc s q (MF.focr {Γ₁ = Γ} (just (.(` _) , snd)) rf MF.ax refl)) =
--  foc s q (focl {Γ₁ = ∘cxt Γ} tt blurl (focr {Γ₁ = ∘cxt Γ} (just _) (max-rf rf) ax refl refl tt) refl refl tt)

-- -- focL + focR + unfoc
max (MF.foc s q (MF.focl {Γ₀ = Γ₀} q₁ lf (MF.focr {Γ₀ = Γ₁}{Γ₂} (just (M , m)) rf (MF.unfoc ok f) refl) refl)) =
  foc s q (focl {Γ₀ = ∘cxt Γ₀} {∘cxt (Γ₁ ++ Γ₂)} q₁ (max-lf lf) (focr {Γ₀ = ∘cxt Γ₁} {∘cxt Γ₂} (just (M , m)) (max-rf rf) (unfoc ok (max f)) refl refl tt) refl refl tt)
-- -- focL + focR + unfoc
max (MF.foc s q (MF.focr {Γ₁ = Γ₂} (just (M , m)) rf (MF.focl {Γ₀ = Γ₀}{Γ₁} q₁ lf (MF.unfoc ok f) refl) refl)) =
  foc s q (focl {Γ₀ = ∘cxt Γ₀} {∘cxt (Γ₁ ++ Γ₂)} q₁ (max-lf lf) (focr {Γ₀ = ∘cxt Γ₁} {∘cxt Γ₂} (just (M , m)) (max-rf rf) (unfoc ok (max f)) refl refl tt) refl refl tt)

-- -- focL + focR + ax
max (MF.foc s q (MF.focl {Γ₀ = Γ₀} {Γ₁} q₁ lf (MF.focr (just (` X , m)) rf MF.ax refl) refl)) =
  foc s q (focl {Γ₀ = ∘cxt Γ₀} {∘cxt Γ₁} q₁ (max-lf lf) (focr {Γ₀ = []} {∘cxt Γ₁} (just (` X , m)) (max-rf rf) ax refl refl tt) refl refl tt)
-- -- focR + focL + ax
max (MF.foc s q (MF.focr {Γ₀ = Γ₀} {Γ₁} (just (` X , m)) rf (MF.focl q₁ lf MF.ax refl) refl)) =
  foc s q (focl {Γ₀ = ∘cxt Γ₀} {∘cxt Γ₁} q₁ (max-lf lf) (focr {Γ₀ = []} {∘cxt Γ₁} (just (` X , m)) (max-rf rf) ax refl refl tt) refl refl tt)

-- -- focR with right-focusing ending in IR
max (MF.foc s q (MF.focr {Γ₀ = Γ₀}{Γ₁} ─ rf (refl , refl) refl)) = foc s q (focr {Γ₀ = ∘cxt Γ₀} {∘cxt Γ₁} nothing (max-rf rf) (refl , refl) refl refl tt)

-- hard cases!!

-- -- focL + unfoc
max (MF.foc s q (MF.focl {Γ₀ = Γ₀} {Γ₁} q₁ lf (MF.unfoc ok f) refl)) = only-lf⇑ (∘cxt Γ₁) s q₁ (max-lf lf) (max f)

-- -- focR + unfoc
max (MF.foc s q (MF.focr {Γ₀ = Γ₀} (just (M , m)) rf (MF.unfoc ok f) refl)) = only-rf⇑ (∘cxt Γ₀) m q (max-rf rf) (max f)



max-lf (MF.pass lf) = pass (max-lf lf)
max-lf (MF.⊸l+ Γ₀ Ξ q fs lf refl) = ⊸l+ Γ₀ Ξ q (maxs fs) (max-lf lf)
max-lf MF.blurl = blurl

max-rf MF.Ir = Ir
max-rf (MF.⊗r+ Δ₀ Ξ m rf gs refl) = ⊗r+ Δ₀ Ξ m (max-rf rf) (maxs gs)
max-rf MF.blurr = blurr

maxs [] = []
maxs (f ∷ fs) = max f ∷ maxs fs
