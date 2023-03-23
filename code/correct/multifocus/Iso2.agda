{-# OPTIONS --rewriting #-}

module correct.multifocus.Iso2 where

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
open import correct.multifocus.EqComplete

cong⊗r⋆₁ : ∀ {S Γ A Ξ} {f g : S ∣ Γ ⊢ A} → f ≗ g
  → (gs : All (λ ΓA → ─ ∣ proj₁ ΓA ⊢ proj₂ ΓA) Ξ)
  → ⊗r⋆ f gs ≗ ⊗r⋆ g gs
cong⊗r⋆₁ eq [] = eq
cong⊗r⋆₁ eq (g' ∷ gs) = cong⊗r⋆₁ (⊗r eq refl) gs

data _≗s_ : ∀ {Ξ} (fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⊢ proj₂ ΔB) Ξ) → Set where
  [] : [] ≗s []
  _∷_ : ∀ {Δ B Ξ} {f g : ─ ∣ Δ ⊢ B} (eq : f ≗ g)
          {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⊢ proj₂ ΔB) Ξ} (eqs : fs ≗s gs) →
          (f ∷ fs) ≗s (g ∷ gs) 

refl≗s' : ∀ {Ξ} (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⊢ proj₂ ΔB) Ξ) → fs ≗s fs
refl≗s' [] = []
refl≗s' (f ∷ fs) = refl ∷ refl≗s' fs

refl≗s : ∀ {Ξ} {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⊢ proj₂ ΔB) Ξ} → fs ≡ gs → fs ≗s gs
refl≗s refl = refl≗s' _

cong⊗r⋆₂ : ∀ {S Γ A Ξ} (f : S ∣ Γ ⊢ A)
  → {fs gs : All (λ ΓA → ─ ∣ proj₁ ΓA ⊢ proj₂ ΓA) Ξ}
  → fs ≗s gs
  → ⊗r⋆ f fs ≗ ⊗r⋆ f gs
cong⊗r⋆₂ _ [] = refl
cong⊗r⋆₂ f {_ ∷ fs} (eq ∷ eqs) = cong⊗r⋆₁ (⊗r refl eq) fs • cong⊗r⋆₂ (⊗r f _) eqs

⊗r⋆pass : ∀ {Γ A' A Ξ} (f : just A' ∣ Γ ⊢ A)
  → (gs : All (λ ΓA → ─ ∣ proj₁ ΓA ⊢ proj₂ ΓA) Ξ)
  → ⊗r⋆ (pass f) gs ≗ pass (⊗r⋆ f gs)
⊗r⋆pass _ [] = refl
⊗r⋆pass f (g ∷ gs) = cong⊗r⋆₁ ⊗rpass gs • ⊗r⋆pass (⊗r f g) gs

cong-embrf : ∀ {S Γ₀ Γ₁ M C m} 
  → (rf : just (M , m) ⇛rf Γ₁ ； C)
  → {f g : S ∣ Γ₀ ⊢ M} → f ≗ g
  → embrf _ rf f ≗ embrf _ rf g
cong-embrf (⊗r+ Δ₀ Ξ m rf gs refl) eq = cong⊗r⋆₁ (cong-embrf rf eq) (embs⇑ gs)
cong-embrf blurr eq = eq

embrf-pass : ∀ {Γ₀ Γ₁ M A C m} 
  → (rf : just (M , m) ⇛rf Γ₁ ； C)
  → (f : just A ∣ Γ₀ ⊢ M) 
  → embrf _ rf (pass f) ≗ pass (embrf _ rf f)
embrf-pass (⊗r+ Δ₀ Ξ m rf gs refl) f =
  cong⊗r⋆₁ (embrf-pass rf f) (embs⇑ gs) • ⊗r⋆pass (embrf _ rf f) (embs⇑ gs)
embrf-pass blurr f = refl

embpass⇑ : ∀ {Γ A C}
  → (f : just A ∣ Γ ⇑ C)
  → emb⇑ (pass⇑ f) ≗ pass (emb⇑ f)

embpass⇓ : ∀ {b Γ A C}
  → (f : [ ∘ , b ] just A ∣ Γ ⇓ C)
  → emb⇓ (pass⇓ f) ≗ pass (emb⇓ f)

embpass⇓ (focl q lf f refl) = refl
embpass⇓ (focr (just (M , m)) rf f refl) =
  cong-embrf rf (embpass⇓ f) • embrf-pass rf (emb⇓ f)
embpass⇓ {∙} (unfoc ok f) = embpass⇑ f

embpass⇑ (⊸r f) = ⊸r (embpass⇑ f) • ⊸rpass
embpass⇑ (Il q f) = refl
embpass⇑ (⊗l q f) = refl
embpass⇑ (foc s q f) = embpass⇓ f

embIl⇑ : ∀ {Γ C} (f :  ─ ∣ Γ ⇑ C) → emb⇑ (Il⇑ f) ≗ Il (emb⇑ f)
embIl⇑ (⊸r f) = ⊸r (embIl⇑ f) • ⊸rIl
embIl⇑ (foc s q f) = refl

emb⊗l⇑ : ∀ {Γ A B C} (f :  just A ∣ B ∷ Γ ⇑ C) → emb⇑ (⊗l⇑ f) ≗ ⊗l (emb⇑ f)
emb⊗l⇑ (⊸r f) = ⊸r (emb⊗l⇑ f) • ⊸r⊗l
emb⊗l⇑ (Il q f) = refl
emb⊗l⇑ (⊗l q f) = refl
emb⊗l⇑ (foc s q f) = refl

⊗r⋆Il : {Γ : Cxt} {A : Fma} {Ξ : List (Cxt × Fma)}
      (f : ─ ∣ Γ ⊢ A)
      (gs : All (λ ΓA → ─ ∣ proj₁ ΓA ⊢ proj₂ ΓA) Ξ) →
      ⊗r⋆ (Il f) gs ≗ Il (⊗r⋆ f gs)
⊗r⋆Il f [] = refl
⊗r⋆Il f (g ∷ gs) =
  cong⊗r⋆₁ ⊗rIl gs • ⊗r⋆Il (⊗r f g) gs

⊗r⋆⊗l : {Γ : Cxt} {A B C : Fma} {Ξ : List (Cxt × Fma)}
      (f : just A ∣ B ∷ Γ ⊢ C)
      (gs : All (λ ΓA → ─ ∣ proj₁ ΓA ⊢ proj₂ ΓA) Ξ) →
      ⊗r⋆ (⊗l f) gs ≗ ⊗l (⊗r⋆ f gs)
⊗r⋆⊗l f [] = refl
⊗r⋆⊗l f (g ∷ gs) =
  cong⊗r⋆₁ ⊗r⊗l gs • ⊗r⋆⊗l (⊗r f g) gs

emb⊸r⋆⇑ : {S : Stp} {Γ : Cxt} (Δ : Cxt) {A : Fma}
      (f : S ∣ Γ ++ Δ ⇑ A) →
      emb⇑ (⊸r⋆⇑ Δ f) ≗ ⊸r⋆ Δ (emb⇑ f)
emb⊸r⋆⇑ [] f = refl
emb⊸r⋆⇑ {Γ = Γ} (_ ∷ Δ) f = ⊸r (emb⊸r⋆⇑ {Γ = Γ ∷ʳ _} Δ f)

emb⊗r+⇑N : ∀ {S Γ₀ Γ} Γ₁ {Δ₀ A B₀ n Ξ}
  → (f : S ∣ Γ ⇑ A)
  → (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ))
  → (eq : Γ ≡ Γ₀ ++ Γ₁)
  → emb⇑ (⊗r+⇑N Γ₁ Δ₀ n Ξ f gs eq) ≗ ⊗r⋆ (⊸r⋆ Γ₁ (emb⇑ (subst⇑ f eq))) (embs⇑ gs)
emb⊗r+⇑N Γ₁ (⊸r f) gs refl =
  emb⊗r+⇑N (Γ₁ ∷ʳ _) f gs refl • cong⊗r⋆₁ (⊸r⋆⊸r _ _) (embs⇑ gs)
emb⊗r+⇑N Γ₁ (Il q f) gs refl =
  Il (emb⊗r+⇑N Γ₁ f gs refl)
  • ~ ⊗r⋆Il (⊸r⋆ Γ₁ (emb⇑ f)) (embs⇑ gs)
  • cong⊗r⋆₁ (~ (⊸r⋆Il Γ₁)) (embs⇑ gs)
emb⊗r+⇑N Γ₁ (⊗l q f) gs refl = 
  ⊗l (emb⊗r+⇑N Γ₁ f gs refl)
  • ~ ⊗r⋆⊗l (⊸r⋆ Γ₁ (emb⇑ f)) (embs⇑ gs)
  • cong⊗r⋆₁ (~ (⊸r⋆⊗l Γ₁)) (embs⇑ gs)
emb⊗r+⇑N Γ₁ (foc s q f) gs refl =
  cong⊗r⋆₁ (emb⊸r⋆⇑ Γ₁ (foc s q f)) (embs⇑ gs)

cong⊸l⋆₂ : {Δ : Cxt} {B C : Fma}
          {Ξ : List (Cxt × Fma)}
          (fs : All (λ ΓA → ─ ∣ proj₁ ΓA ⊢ proj₂ ΓA) Ξ)
          {f g : just B ∣ Δ ⊢ C} → f ≗ g →
          ⊸l⋆ fs f ≗ ⊸l⋆ fs g
cong⊸l⋆₂ [] eq = eq
cong⊸l⋆₂ (f ∷ fs) eq = ⊸l refl (cong⊸l⋆₂ fs eq)

cong-emblf : ∀ {S Γ₀ Γ₁ C Q} {q : isPosAt Q}
 → (lf : q ⇛lf S ； Γ₀)
 → {f g : just Q ∣ Γ₁ ⊢ C} → f ≗ g
 → emblf q lf f ≗ emblf q lf g
cong-emblf (pass lf) eq = pass (cong-emblf lf eq)
cong-emblf (⊸l+ Γ₀ Ξ q fs lf refl) eq = cong⊸l⋆₂ (embs⇑ fs) (cong-emblf lf eq)
cong-emblf blurl eq = eq

⊗r⊸l⋆ : {Δ Λ : Cxt} {A B B' : Fma} {Ξ : List (Cxt × Fma)}
    → (fs : All (λ ΓA → ─ ∣ proj₁ ΓA ⊢ proj₂ ΓA) Ξ) {f : just B' ∣ Δ ⊢ A} {g : ─ ∣ Λ ⊢ B}
    → ⊗r (⊸l⋆ fs f) g ≗ ⊸l⋆ fs (⊗r f g)
⊗r⊸l⋆ [] = refl
⊗r⊸l⋆ (f' ∷ fs) = ⊗r⊸l • ⊸l refl (⊗r⊸l⋆ fs)

emblf⊗r : ∀ {S Γ₀ Γ₁ Δ A B Q q}
 → (lf : q ⇛lf S ； Γ₀)
 → (f : just Q ∣ Γ₁ ⊢ A)          
 → (g : ─ ∣ Δ ⊢ B)          
 → emblf q lf (⊗r f g) ≗ ⊗r (emblf q lf f) g
emblf⊗r (pass lf) f g = pass (emblf⊗r lf f g) • ~ ⊗rpass
emblf⊗r (⊸l+ Γ₀ Ξ q fs lf refl) f g =
  cong⊸l⋆₂ (embs⇑ fs) (emblf⊗r lf f g) • (~ ⊗r⊸l⋆ (embs⇑ fs))
emblf⊗r blurl f g = refl

emblf⊗r⋆ : ∀ {S Γ₀ Γ₁ A Ξ Q q}
 → (lf : q ⇛lf S ； Γ₀)
 → (f : just Q ∣ Γ₁ ⊢ A)          
 → (gs : All (λ ΓA → ─ ∣ proj₁ ΓA ⊢ proj₂ ΓA) Ξ)
 → emblf q lf (⊗r⋆ f gs) ≗ ⊗r⋆ (emblf q lf f) gs
emblf⊗r⋆ lf f [] = refl
emblf⊗r⋆ lf f (g ∷ gs) =
  emblf⊗r⋆ lf (⊗r f g) gs
  • cong⊗r⋆₁ (emblf⊗r lf f g) gs

⊗r⋆⊗r⋆ : {S : Stp} {Γ : Cxt} {A : Fma}
      {Ξ Ξ' : List (Cxt × Fma)}
      (f : S ∣ Γ ⊢ A)
      (fs : All (λ ΓA → ─ ∣ proj₁ ΓA ⊢ proj₂ ΓA) Ξ) → 
      (gs : All (λ ΓA → ─ ∣ proj₁ ΓA ⊢ proj₂ ΓA) Ξ') →
      ⊗r⋆ f (fs ++All gs) ≡ ⊗r⋆ (⊗r⋆ f fs) gs
⊗r⋆⊗r⋆ f [] gs = refl
⊗r⋆⊗r⋆ f (f' ∷ fs) gs = ⊗r⋆⊗r⋆ (⊗r f f') fs gs

embs⇑++ : ∀ {Ξ Ξ'} (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ)
  → (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ')
  → embs⇑ (fs ++All gs) ≡ embs⇑ fs ++All embs⇑ gs
embs⇑++ [] gs = refl
embs⇑++ (f ∷ fs) gs = cong (_ ∷_) (embs⇑++ fs gs)

embrf++rf : ∀ {S Δ} {Δ₀ : Cxt} {Γ : Cxt} {B₀ C : Fma} {Ξ : List (Cxt × Fma)}
       {s : Maybe (Σ Fma isNegAt)}
       (rf : s ⇛rf Γ ； C)
       (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ))
       (h : end-rf? _∣_⊢_ S Δ s) → 
       embrf s (++rf Δ₀ Ξ s rf gs) h ≗ ⊗r⋆ (embrf s rf h) (embs⇑ gs)
embrf++rf Ir gs (refl , refl) = refl
embrf++rf {s = just x} (⊗r+ Δ₀ Ξ m rf gs₁ refl) gs h =
  cong⊗r⋆₂  (embrf (just x) rf h) (refl≗s (embs⇑++ gs₁ gs))
  • refl≗ (⊗r⋆⊗r⋆ (embrf (just x) rf h) (embs⇑ gs₁) (embs⇑ gs))
embrf++rf {s = ─} (⊗r+ Δ₀ Ξ m rf gs₁ refl) gs (refl , refl) =
  cong⊗r⋆₂  (embrf nothing rf _) (refl≗s (embs⇑++ gs₁ gs))
  • refl≗ (⊗r⋆⊗r⋆ (embrf nothing rf _) (embs⇑ gs₁) (embs⇑ gs))

embrf++rf blurr gs h = refl
 
emb⊗r+⇑Q : ∀ {S Γ Δ₀ B₀ Q p Ξ}
  → (f : S ∣ Γ ⇑ Q)
  → (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ))
  → emb⇑ (⊗r+⇑Q Δ₀ p Ξ f gs) ≗ ⊗r⋆ (emb⇑ f) (embs⇑ gs)

emb⊗r+⇓Q : ∀ {b S Γ Δ₀ B₀ Q p Ξ}
  → (f : [ b , ∘ ] S ∣ Γ ⇓ Q)
  → (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ))
  → emb⇓ (⊗r+⇓Q Δ₀ p Ξ f gs) ≗ ⊗r⋆ (emb⇓ f) (embs⇑ gs)

emb⊗r+⇑Q (Il q f) gs =
  Il (emb⊗r+⇑Q f gs) • (~ (⊗r⋆Il (emb⇑ f) (embs⇑ gs)))
emb⊗r+⇑Q (⊗l q f) gs = 
  ⊗l (emb⊗r+⇑Q f gs) • (~ (⊗r⋆⊗l (emb⇑ f) (embs⇑ gs)))
emb⊗r+⇑Q (foc s q f) gs = emb⊗r+⇓Q f gs

emb⊗r+⇓Q (focl q lf f refl) gs =
  cong-emblf lf (emb⊗r+⇓Q f gs) • emblf⊗r⋆ lf (emb⇓ f) (embs⇑ gs)
emb⊗r+⇓Q (focr (just (M , m)) rf f refl) gs =
  embrf++rf rf gs (emb⇓ f) 
emb⊗r+⇓Q (focr ─ rf f refl) gs = embrf++rf rf gs f
emb⊗r+⇓Q {∙} {just P} (unfoc ok f) gs = emb⊗r+⇑Q f gs

emb⊗r+⇑ : ∀ {S Γ Δ₀ B₀ A Ξ} (f : S ∣ Γ ⇑ A) 
  → (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ))
  → emb⇑ (⊗r+⇑ Δ₀ Ξ f gs) ≗ ⊗r⋆ (emb⇑ f) (embs⇑ gs)
emb⊗r+⇑ {A = ` X} f gs = emb⊗r+⇑Q f gs
emb⊗r+⇑ {A = I} f gs = emb⊗r+⇑Q f gs
emb⊗r+⇑ {A = A ⊗ B} f gs = emb⊗r+⇑Q f gs
emb⊗r+⇑ {A = A ⊸ B} f gs = emb⊗r+⇑N [] f gs refl

emb⊸l+⇑ : ∀ {Γ₀ Δ A₀ B C Ξ}
  → (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ))
  → (f : just B ∣ Δ ⇑ C)
  → emb⇑ (⊸l+⇑ Γ₀ Ξ fs f) ≗ ⊸l⋆ (embs⇑ fs) (emb⇑ f)
emb⊸l+⇑ {B = ` X} fs f = {!!}
emb⊸l+⇑ {B = I} fs f = {!!}
emb⊸l+⇑ {B = A ⊗ B} fs f = {!!}
emb⊸l+⇑ {B = A ⊸ B} fs f = {!!}

emb⇑∘focus : ∀ {S Γ A} (f : S ∣ Γ ⊢ A) → emb⇑ (focus f) ≗ f
emb⇑∘focus ax = refl
emb⇑∘focus (pass f) = embpass⇑ (focus f) • pass (emb⇑∘focus f)
emb⇑∘focus Ir = refl
emb⇑∘focus (Il f) = embIl⇑ (focus f) • Il (emb⇑∘focus f)
emb⇑∘focus (⊗r f g) =
  emb⊗r+⇑ (focus f) (focus g ∷ []) • ⊗r (emb⇑∘focus f) (emb⇑∘focus g)
emb⇑∘focus (⊗l f) = emb⊗l⇑ (focus f) • ⊗l (emb⇑∘focus f)
emb⇑∘focus (⊸r f) = ⊸r (emb⇑∘focus f)
emb⇑∘focus (⊸l f g) =
  emb⊸l+⇑ (focus f ∷ []) (focus g) • ⊸l (emb⇑∘focus f) (emb⇑∘focus g)
