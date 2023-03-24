{-# OPTIONS --rewriting #-}

module correct.multifocus.EqSound where

open import Data.List hiding (concat)
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
open import correct.multifocus.Iso2

cong⊸l⋆₁ : {Δ : Cxt} {B C : Fma}
          {Ξ : List (Cxt × Fma)}
          {fs gs : All (λ ΓA → ─ ∣ proj₁ ΓA ⊢ proj₂ ΓA) Ξ} → fs ≗s gs →
          {f : just B ∣ Δ ⊢ C} → 
          ⊸l⋆ fs f ≗ ⊸l⋆ gs f
cong⊸l⋆₁ [] = refl
cong⊸l⋆₁ (eq ∷ eqs) = ⊸l eq (cong⊸l⋆₁ eqs)

emb-runL : ∀ {S Γ Δ A C} (ℓ : L S Γ A)
  → (f : S ∣ Γ ++ Δ ⇑ C)
  → emb⇑ (runL {Δ = Δ} ℓ f) ≗ runL' ℓ (emb⇑ f)
emb-runL done f = refl
emb-runL (Il-1 ℓ) f = emb-runL ℓ (Il⇑ f) • cong-runL' ℓ (embIl⇑ f)
emb-runL (⊗l-1 ℓ) f = emb-runL ℓ (⊗l⇑ f) • cong-runL' ℓ (emb⊗l⇑ f)

emblf⊸r : ∀ {S Γ₀ Γ₁ A C Q q}
 → (lf : q ⇛lf S ； Γ₀)
 → (f : just Q ∣ Γ₁ ∷ʳ A ⊢ C)          
 → emblf q lf (⊸r f) ≗ ⊸r (emblf q lf f)
emblf⊸r (pass lf) f =
  pass (emblf⊸r lf f) • (~ ⊸rpass)
emblf⊸r (⊸l+ Γ₀ Ξ q fs lf refl) f =
  cong⊸l⋆₂ (embs⇑ fs) (emblf⊸r lf f) • (~ (⊸r⊸l⋆ _))
emblf⊸r blurl f = refl

emblf⊸r⋆ : ∀ {S Γ₀ Γ₁} Δ {C Q q}
 → (lf : q ⇛lf S ； Γ₀)
 → (f : just Q ∣ Γ₁ ++ Δ ⊢ C)          
 → emblf q lf (⊸r⋆ Δ f) ≗ ⊸r⋆ Δ (emblf q lf f)
emblf⊸r⋆ [] lf f = refl
emblf⊸r⋆ {Γ₁ = Γ₁} (A ∷ Δ) lf f =
  emblf⊸r lf (⊸r⋆ Δ f) •  ⊸r (emblf⊸r⋆ {Γ₁ = Γ₁ ∷ʳ _} Δ lf f)

embrfIl : ∀ {Γ₀ Γ₁ C M m} 
  → (rf : _ ⇛rf Γ₁ ； C)
  → (f : ─ ∣ Γ₀ ⊢ M)
  → embrf (just (M , m)) rf (Il f) ≗ Il (embrf (just (M , m)) rf f)
embrfIl (⊗r+ Δ₀ Ξ m rf gs refl) f =
  cong⊗r⋆₁ (embrfIl rf f) (embs⇑ gs) • ⊗r⋆Il _ (embs⇑ gs) 
embrfIl blurr f = refl

embrf⊗l : ∀ {Γ₀ Γ₁ A B C M m} 
  → (rf : _ ⇛rf Γ₁ ； C)
  → (f : just A ∣ B ∷ Γ₀ ⊢ M)
  → embrf (just (M , m)) rf (⊗l f) ≗ ⊗l (embrf (just (M , m)) rf f)
embrf⊗l (⊗r+ Δ₀ Ξ m rf gs refl) f =
  cong⊗r⋆₁ (embrf⊗l rf f) (embs⇑ gs) • ⊗r⋆⊗l _ (embs⇑ gs) 
embrf⊗l blurr f = refl

embrf-runL' : ∀ {S Γ₀ Γ₁ Δ A C M m} 
  → (rf : just (M , m) ⇛rf Γ₁ ； C)
  → (f : S ∣ Δ ++ Γ₀ ⊢ M)
  → (ℓ : L S Δ A)
  → embrf (just (M , m)) rf (runL' {Δ = Γ₀} ℓ f) ≗ runL' ℓ (embrf (just (M , m)) rf f)
embrf-runL' rf f done = refl
embrf-runL' rf f (Il-1 ℓ) =
  embrf-runL' rf (Il f) ℓ • cong-runL' ℓ (embrfIl rf f)
embrf-runL' rf f (⊗l-1 ℓ) =
  embrf-runL' rf (⊗l f) ℓ • cong-runL' ℓ (embrf⊗l rf f)

emblf-embrf : ∀ {S Γ₀ Γ₁ Γ₂ A M Q q m}
 → (lf : q ⇛lf S ； Γ₀)
 → (rf : just (M , m) ⇛rf Γ₂ ； A)
 → (f : just Q ∣ Γ₁ ⊢ M)
 → emblf q lf (embrf (just (M , m)) rf f) ≗ embrf (just (M , m)) rf (emblf q lf f)
emblf-embrf lf (⊗r+ Δ₀ Ξ m rf gs refl) f =
  emblf⊗r⋆ lf (embrf _ rf f) (embs⇑ gs)
  • cong⊗r⋆₁ (emblf-embrf lf rf f) (embs⇑ gs)
emblf-embrf lf blurr f = refl

emb⇑≗ : ∀ {S Γ A} {f g : S ∣ Γ ⇑ A} → f ≗⇑ g → emb⇑ f ≗ emb⇑ g
emb⇓≗ : ∀ {b c S Γ A} {f g : [ b , c ] S ∣ Γ ⇓ A} → f ≗⇓ g → emb⇓ f ≗ emb⇓ g
embs⇑≗ : ∀ {Ξ} {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ}
  → fs ≗s⇑ gs → embs⇑ fs ≗s embs⇑ gs
cong-emblf₂ : ∀ {S Γ₀ Γ₁ C Q q}
 → {h k : q ⇛lf S ； Γ₀} → h ≗lf k
 → {f : just Q ∣ Γ₁ ⊢ C}
 → emblf q h f ≗ emblf q k f
cong-embrf₂ : ∀ {S Γ₀ Γ₁ C s}
  → {h k : s ⇛rf Γ₁ ； C} → h ≗rf k
  → {f : end-rf? (λ T Γ A → T ∣ Γ ⊢ A) S Γ₀ s}
  → embrf s h f ≗ embrf s k f

cong-emblf₂ refl = refl
cong-emblf₂ (~ eq) = ~ cong-emblf₂ eq
cong-emblf₂ (eq • eq₁) = cong-emblf₂ eq • cong-emblf₂ eq₁
cong-emblf₂ (pass eq) = pass (cong-emblf₂ eq)
cong-emblf₂ (⊸l+ eqs eq {eq = refl}{refl}) =
  cong⊸l⋆₁ (embs⇑≗ eqs) • cong⊸l⋆₂ (embs⇑ _) (cong-emblf₂ eq)

cong-embrf₂ refl = refl
cong-embrf₂ (~ eq) = ~ cong-embrf₂ eq
cong-embrf₂ (eq • eq₁) = cong-embrf₂ eq • cong-embrf₂ eq₁
cong-embrf₂ {s = just x} (⊗r+ eq {gs = gs} eqs {eq = refl} {refl}) =
  cong⊗r⋆₂ _ (embs⇑≗ eqs) • cong⊗r⋆₁ (cong-embrf₂ eq) (embs⇑ gs)
cong-embrf₂ {s = ─} (⊗r+ eq {gs = gs} eqs {eq = refl} {refl}) {refl , refl} =
  cong⊗r⋆₂ _ (embs⇑≗ eqs) • cong⊗r⋆₁ (cong-embrf₂ eq) (embs⇑ gs)

embs⇑≗ [] = []
embs⇑≗ (eq ∷ eqs) = (emb⇑≗ eq) ∷ (embs⇑≗ eqs)

emb⇑≗ refl = refl
emb⇑≗ (~ eq) = ~ emb⇑≗ eq
emb⇑≗ (eq • eq₁) = emb⇑≗ eq • emb⇑≗ eq₁
emb⇑≗ (⊸r eq) = ⊸r (emb⇑≗ eq)
emb⇑≗ (Il eq) = Il (emb⇑≗ eq)
emb⇑≗ (⊗l eq) = ⊗l (emb⇑≗ eq)
emb⇑≗ (foc eq) = emb⇓≗ eq

emb⇓≗ refl = refl
emb⇓≗ (~ eq) = ~ emb⇓≗ eq
emb⇓≗ (eq • eq₁) = emb⇓≗ eq • emb⇓≗ eq₁
emb⇓≗ (focl {h = h} eql {eq = refl}{refl} eq) =
  cong-emblf h (emb⇓≗ eq) • cong-emblf₂ eql
emb⇓≗ (focr {h = h} eqr {eq = refl}{refl} eq) = 
  cong-embrf h (emb⇓≗ eq) • cong-embrf₂ eqr
emb⇓≗ (focrn eqr {refl , refl}{refl , refl} {eq = refl} {refl}) =
  cong-embrf₂ eqr
emb⇓≗ (unfoc eq) = emb⇑≗ eq
emb⇓≗ (swap {lf = lf}{rf}) = emblf-embrf lf rf _
emb⇓≗ (early-lf Δ r {lf = lf} {f = f} {eq = refl}{refl}) =
  emb⊸r⋆⇑ Δ _
  • ~ emblf⊸r⋆ Δ lf (emb⇑ f)
  • cong-emblf lf (~ emb⊸r⋆⇑ Δ _)
emb⇓≗ (early-lf-at Δ r {lf = lf} {f = f} {eq = refl}{refl}) = 
  emb⊸r⋆⇑ Δ _
  • ~ emblf⊸r⋆ Δ lf (emb⇓ f)
  • cong-emblf lf (~ emb⊸r⋆⇑ Δ _)
emb⇓≗ (early-rf t {rf = rf} {f = f} ℓ {eq = refl}) =
  emb-runL ℓ _
  • ~ embrf-runL' rf (emb⇑ f) ℓ
  • cong-embrf rf (~ emb-runL ℓ f)
emb⇓≗ (early-rf-at t {rf = rf} {f = f} ℓ {eq = refl}) = 
  emb-runL ℓ _
  • ~ embrf-runL' rf (emb⇓ f) ℓ
  • cong-embrf rf (~ emb-runL ℓ _)
emb⇓≗ blurr-at = refl
emb⇓≗ blurl-at = refl
