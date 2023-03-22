{-# OPTIONS --rewriting #-}

module correct.multifocus.Iso where

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

{-
no-boolr⇓ : ∀{S Γ A} (s : isPosAt A) → [ ∘ , ∙ ] S ∣ Γ ⇓ A → [ ∘ , ∘ ] S ∣ Γ ⇓ A
no-boolr⇓ s (focl q lf ax refl) = focl q lf (focr (just _) blurr ax refl) refl
no-boolr⇓ s (focl q lf (unfoc (inj₁ ok) f) eq) = focl q lf (unfoc ok f) eq
no-boolr⇓ s (focl q lf (unfoc (inj₂ ok) f) eq) = ⊥-elim {!!}
no-boolr⇓ s (unfoc ok f) = ⊥-elim {!!}

no-booll⇓ : ∀{S Γ A} (s : isIrr S) → [ ∙ , ∘ ] S ∣ Γ ⇓ A → [ ∘ , ∘ ] S ∣ Γ ⇓ A
no-booll⇓ s (focr (just _) rf ax refl) = focr (just _) rf (focl tt blurl ax refl) refl
no-booll⇓ {just _} s (focr (just (M , m)) rf (unfoc (inj₁ ok) f) eq) = ⊥-elim {!!}
no-booll⇓ {just _} s (focr (just (M , m)) rf (unfoc (inj₂ ok) f) eq) = focr _ rf (unfoc ok f) eq
no-booll⇓ s (focr ─ rf f eq) = focr (─) rf f eq
no-booll⇓ {just _} s (unfoc ok f) = {!imp!}
-- no-booll⇓ s ax = focl tt blurl ax refl
-- no-booll⇓ s (focl q lf f eq) = focl q lf f eq
-- no-booll⇓ {∘} s (unfoc ok f) = unfoc ok f
-- no-booll⇓ {∙} {just A} s (unfoc (inj₁ ok) f) = ⊥-elim (pos×negat→⊥ ok s)
-- no-booll⇓ {∙} {just A} s (unfoc (inj₂ ok) f) = unfoc ok f

-- no-boolr⇓ : ∀{c S Γ Q} (q : isPosAt Q) → [ ∙ , c ] S ∣ Γ ⇓ Q → [ ∙ , ∘ ] S ∣ Γ ⇓ Q
-- no-boolr⇓ q ax = focr (just _) blurr ax refl
-- no-boolr⇓ q (focr s rf f eq) = focr s rf f eq
-- no-boolr⇓ {∘} q (unfoc ok f) = unfoc ok f
-- no-boolr⇓ {∙} {just A} q (unfoc (inj₁ ok) f) = unfoc ok f
-- no-boolr⇓ {∙} {just A} q (unfoc (inj₂ ok) f) = ⊥-elim (neg×posat→⊥ ok q)

no-bools⇓ : ∀{b c S Γ Q} (s : isIrr S) (q : isPosAt Q) → [ b , c ] S ∣ Γ ⇓ Q → [ ∘ , ∘ ] S ∣ Γ ⇓ Q
no-bools⇓ {∘} {∘} s q f = f
no-bools⇓ {∘} {∙} s q f = no-boolr⇓ q f
no-bools⇓ {∙} {∘} s q f = no-booll⇓ s f
no-bools⇓ {∙} {∙} s q ax = focl tt blurl (focr (just _) blurr ax refl) refl
no-bools⇓ {∙} {∙} {just A} s q (unfoc ok f) = {!imp!}

-- -- no-bools⇓ : ∀{b c S Γ Q} (s : isIrr S) (q : isPosAt Q) → [ b , c ] S ∣ Γ ⇓ Q → [ ∘ , ∘ ] S ∣ Γ ⇓ Q
-- -- no-bools⇓ s q ax = focl tt blurl (focr (just _) blurr ax refl) refl
-- -- no-bools⇓ s q (focl q' lf f eq) = focl q' lf (no-boolr⇓ q f) eq
-- -- no-bools⇓ s q (focr (just (M , m)) rf f eq) = focr (just (M , m)) rf (no-booll⇓ s f) eq
-- -- no-bools⇓ s q (focr ─ rf f eq) = focr nothing rf f eq
-- -- no-bools⇓ {∘} {∙} s q (unfoc ok f) = ⊥-elim (neg×posat→⊥ ok q)
-- -- no-bools⇓ {∙} {∘} {just _} s q (unfoc ok f) = ⊥-elim (pos×negat→⊥ ok s)
-- -- no-bools⇓ {∙} {∙} {just _} s q (unfoc (inj₁ ok) f) = ⊥-elim (pos×negat→⊥ ok s)
-- -- no-bools⇓ {∙} {∙} {just _} s q (unfoc (inj₂ ok) f) = ⊥-elim (neg×posat→⊥ ok q)
-}

++lf++ : ∀ {Γ₀ Γ₁ Γ A₀ A₁ B Q Ξ Ξ'} {q : isPosAt Q}
          (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ))
          (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₁ , A₁) ∷ Ξ'))
          (h : q ⇛lf just B ； Γ) →
          ++lf Γ₀ (Ξ ++ (Γ₁ , A₁) ∷ Ξ') q h (fs ++All gs) ≡
            ++lf Γ₀ Ξ q (++lf Γ₁ Ξ' q h gs) fs
++lf++ {Γ₁}{Γ₂} {Ξ = Ξ₁}{Ξ'} fs gs (⊸l+ Γ₀ Ξ q fs₁ h refl) =
  cong (λ x → ⊸l+ Γ₁ (Ξ₁ ++ (Γ₂ , _) ∷ Ξ' ++ (Γ₀ , _) ∷ Ξ) q x h refl) (++Allass fs gs fs₁)
++lf++ fs gs blurl = refl

++⊸l+⇑P : ∀ {S Γ₀ Γ₁ Δ Δ₀ Δ₁ A₀ A₁ B C Ξ Ξ' p}
          (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ))
          (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₁ , A₁) ∷ Ξ'))
          (f : S ∣ Δ ⇑ C)
          (eq : Δ ≡ Δ₀ ++ Δ₁)
          (ℓ : L S Δ₀ B) →
          ⊸l+⇑P Γ₀ Δ₀ Δ₁ p (Ξ ++ (Γ₁ , A₁) ∷ Ξ') (fs ++All gs) f eq ℓ 
             ≡ ⊸l+⇑M Γ₀ tt Ξ fs (⊸l+⇑P Γ₁ Δ₀ Δ₁ p Ξ' gs f eq ℓ)
++⊸l+⇑P fs gs (⊸r f) refl ℓ = cong ⊸r (++⊸l+⇑P fs gs f refl ℓ)
++⊸l+⇑P fs gs (Il q f) refl ℓ = ++⊸l+⇑P fs gs f refl (Il-1 ℓ)
++⊸l+⇑P fs gs (⊗l q f) refl ℓ = ++⊸l+⇑P fs gs f refl (⊗l-1 ℓ)
++⊸l+⇑P fs gs (foc s q f) refl ℓ = refl

++⊸l+⇑M : ∀ {Γ₀ Γ₁ Δ A₀ A₁ B C Ξ Ξ' m}
          (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ))
          (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₁ , A₁) ∷ Ξ'))
          (f : just B ∣ Δ ⇑ C) →
          ⊸l+⇑M Γ₀ m (Ξ ++ (Γ₁ , A₁) ∷ Ξ') (fs ++All gs) f
             ≡ ⊸l+⇑M Γ₀ tt Ξ fs (⊸l+⇑M Γ₁ m Ξ' gs f)

++⊸l+⇓M : ∀ {b Γ₀ Γ₁ Δ A₀ A₁ B C Ξ Ξ' m}
          (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ))
          (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₁ , A₁) ∷ Ξ'))
          (f : [ ∘ , b ] just B ∣ Δ ⇓ C) →
          ⊸l+⇓M Γ₀ m (Ξ ++ (Γ₁ , A₁) ∷ Ξ') (fs ++All gs) f
             ≡ ⊸l+⇓M Γ₀ tt Ξ fs (⊸l+⇓M Γ₁ m Ξ' gs f)

++⊸l+⇑M fs gs (⊸r f) = cong ⊸r (++⊸l+⇑M fs gs f)
++⊸l+⇑M fs gs (foc s q f) = cong (foc tt q) (++⊸l+⇓M fs gs f)

++⊸l+⇓M {Γ₀ = Γ₀}{Γ₁} {Ξ = Ξ} {Ξ'} fs gs (focl q lf f refl) =
  cong (λ x → focl q x f refl)
       {x = ++lf Γ₀ (Ξ ++ (Γ₁ , _) ∷ Ξ') q lf (fs ++All gs)}
       {++lf Γ₀ Ξ q (++lf Γ₁ Ξ' q lf gs) fs}
       (++lf++ fs gs lf)
++⊸l+⇓M {Γ₀ = Γ₀}{Γ₁} {Ξ = Ξ} {Ξ'} fs gs (focr (just x) rf f refl) =
  cong (λ y → focr (just x) rf y refl)
       {x = ⊸l+⇓M Γ₀ _ (Ξ ++ (Γ₁ , _) ∷ Ξ') (fs ++All gs) f}
       {⊸l+⇓M Γ₀ tt Ξ fs (⊸l+⇓M Γ₁ _ Ξ' gs f)}
       (++⊸l+⇓M fs gs f)
++⊸l+⇓M {∙} fs gs (unfoc ok f) = cong (unfoc ok) (++⊸l+⇑M fs gs f)

++⊸l+⇑ : ∀ {Γ₀ Γ₁ Δ A₀ A₁ B C Ξ Ξ'}
          (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ))
          (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₁ , A₁) ∷ Ξ'))
          (f : just B ∣ Δ ⇑ C) →
          ⊸l+⇑ Γ₀ (Ξ ++ (Γ₁ , A₁) ∷ Ξ') (fs ++All gs) f
            ≡ ⊸l+⇑ Γ₀ Ξ fs (⊸l+⇑ Γ₁ Ξ' gs f)
++⊸l+⇑ {B = ` X} fs gs f = ++⊸l+⇑M fs gs f
++⊸l+⇑ {B = I} fs gs f = ++⊸l+⇑P fs gs f refl done
++⊸l+⇑ {B = A ⊗ B} fs gs f = ++⊸l+⇑P fs gs f refl done
++⊸l+⇑ {B = A ⊸ B} fs gs f = ++⊸l+⇑M fs gs f

++⊗r+⇑N : ∀ {S Γ Γ₀ Γ₁ Δ₀ Δ₁ B₀ B₁ A Ξ Ξ' n}
          (f : S ∣ Γ ⇑ A)
          (eq : Γ ≡ Γ₀ ++ Γ₁)
          (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)) →
          (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₁ , B₁) ∷ Ξ')) →
          ⊗r+⇑N Γ₁ Δ₀ n (Ξ ++ (Δ₁ , B₁) ∷ Ξ') f (fs ++All gs) eq
            ≡ ⊗r+⇑Q Δ₁ (isPosAt⊗⋆ tt (fmas Ξ)) Ξ' (⊗r+⇑N Γ₁ Δ₀ n Ξ f fs eq) gs
++⊗r+⇑N (⊸r f) refl fs gs = ++⊗r+⇑N f refl fs gs
++⊗r+⇑N {Γ₁ = Γ₁} (Il q f) refl fs gs =
  trans (cong (λ x → Il x (⊗r+⇑N Γ₁ _ _ _ f (fs ++All gs) refl)) (isProp-isPosAt _ _))
        (cong (Il _) (++⊗r+⇑N f refl fs gs))
++⊗r+⇑N {Γ₁ = Γ₁} (⊗l q f) refl fs gs = 
  trans (cong (λ x → ⊗l x (⊗r+⇑N Γ₁ _ _ _ f (fs ++All gs) refl)) (isProp-isPosAt _ _))
        (cong (⊗l _) (++⊗r+⇑N f refl fs gs))
++⊗r+⇑N (foc s q f) refl fs gs =
  cong (λ x → foc s x (focr _ (⊗r+ _ _ _ blurr (fs ++All gs) _) _ refl)) (isProp-isPosAt _ _)

++⊗r+⇓Q : ∀ {b S Γ Δ₀ Δ₁ B₀ B₁ A Ξ Ξ' q}
          (f : [ b , ∘ ] S ∣ Γ ⇓ A)
          (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)) →
          (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₁ , B₁) ∷ Ξ')) →
          ⊗r+⇓Q Δ₀ q (Ξ ++ (Δ₁ , B₁) ∷ Ξ') f (fs ++All gs)
            ≡ ⊗r+⇓Q Δ₁ (isPosAt⊗⋆ tt (fmas Ξ)) Ξ' (⊗r+⇓Q Δ₀ q Ξ f fs) gs

++⊗r+⇑Q : ∀ {S Γ Δ₀ Δ₁ B₀ B₁ A Ξ Ξ' q}
          (f : S ∣ Γ ⇑ A)
          (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)) →
          (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₁ , B₁) ∷ Ξ')) →
          ⊗r+⇑Q Δ₀ q (Ξ ++ (Δ₁ , B₁) ∷ Ξ') f (fs ++All gs)
            ≡ ⊗r+⇑Q Δ₁ (isPosAt⊗⋆ tt (fmas Ξ)) Ξ' (⊗r+⇑Q Δ₀ q Ξ f fs) gs

++⊗r+⇓Q (focl q lf f refl) fs gs =
  cong (λ x → focl q lf x refl) (++⊗r+⇓Q f fs gs)
++⊗r+⇓Q (focr s rf f refl) fs gs =
  cong (λ x → focr s x f refl) {!!}
++⊗r+⇓Q {∙} {just P} (unfoc ok f) fs gs = cong (unfoc ok) (++⊗r+⇑Q f fs gs)

++⊗r+⇑Q (Il q f) fs gs =
  trans (cong (λ x → Il x (⊗r+⇑Q _ _ _ f (fs ++All gs))) (isProp-isPosAt _ _))
        (cong (Il _) (++⊗r+⇑Q f fs gs))
++⊗r+⇑Q (⊗l q f) fs gs = 
  trans (cong (λ x → ⊗l x (⊗r+⇑Q _ _ _ f (fs ++All gs))) (isProp-isPosAt _ _))
        (cong (⊗l _) (++⊗r+⇑Q f fs gs))
++⊗r+⇑Q (foc s q f) fs gs = 
  cong₂ (foc s) (isProp-isPosAt _ _) (++⊗r+⇓Q f fs gs)

⊗r+⇑-posat : ∀ {S Γ Δ₀ B₀ A Ξ q}
             {f : S ∣ Γ ⇑ A}
             {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} →
             ⊗r+⇑ Δ₀ Ξ f fs ≡ ⊗r+⇑Q Δ₀ q Ξ f fs
⊗r+⇑-posat {A = ` X} = refl
⊗r+⇑-posat {A = I} = refl
⊗r+⇑-posat {A = A ⊗ B} = refl

++⊗r+⇑ : ∀ {S Γ Δ₀ Δ₁ B₀ B₁ A Ξ Ξ'}
        (f : S ∣ Γ ⇑ A)
        (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)) →
        (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₁ , B₁) ∷ Ξ')) →
        ⊗r+⇑ Δ₀ (Ξ ++ (Δ₁ , B₁) ∷ Ξ') f (fs ++All gs)
          ≡ ⊗r+⇑ Δ₁ Ξ' (⊗r+⇑ Δ₀ Ξ f fs) gs
++⊗r+⇑ {A = ` X} f fs gs = trans (++⊗r+⇑Q f fs gs) (sym ⊗r+⇑-posat)
++⊗r+⇑ {A = I} f fs gs = trans (++⊗r+⇑Q f fs gs) (sym ⊗r+⇑-posat)
++⊗r+⇑ {A = A ⊗ B} f fs gs = trans (++⊗r+⇑Q f fs gs) (sym ⊗r+⇑-posat)
++⊗r+⇑ {A = A ⊸ B} f fs gs = trans (++⊗r+⇑N f refl fs gs) (sym ⊗r+⇑-posat)

focus⊸l⋆ : {Δ : Cxt} {B C : Fma}
       {Ξ : List (Cxt × Fma)}
       (fs : All (λ ΓA → ─ ∣ proj₁ ΓA ⊢ proj₂ ΓA) Ξ)
       (g : just B ∣ Δ ⊢ C) →
       focus (⊸l⋆ fs g) ≡ ⊸l⋆⇑ (focuss fs) (focus g) 
focus⊸l⋆ [] g = refl
focus⊸l⋆ (f ∷ []) g = refl
focus⊸l⋆ (f ∷ f' ∷ fs) g =
  trans (cong (⊸l⇑ (focus f)) (focus⊸l⋆ (f' ∷ fs) g))
        (sym (++⊸l+⇑ (_ ∷ []) (_ ∷ focuss fs) (focus g)))

focus⊗r⋆ : {S : Stp} {Γ : Cxt} {A : Fma}
      {Ξ : List (Cxt × Fma)}
      (f : S ∣ Γ ⊢ A)
      (gs : All (λ ΓA → ─ ∣ proj₁ ΓA ⊢ proj₂ ΓA) Ξ) →
      focus (⊗r⋆ f gs) ≡ ⊗r⋆⇑ (focus f) (focuss gs)
focus⊗r⋆ f [] = refl
focus⊗r⋆ f (g ∷ []) = refl
focus⊗r⋆ f (g' ∷ g ∷ gs) =
  trans (focus⊗r⋆ (⊗r f g') (g ∷ gs))
        (sym (++⊗r+⇑ (focus f) (focus g' ∷ []) (focuss (g ∷ gs))))


-- ⊸l+⇑-pos : ∀ {Γ₀ Δ A₀ B C Ξ} (p : isPos B)
--          {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)}
--          {f : just B ∣ Δ ⇑ C} → 
--         ⊸l+⇑ Γ₀ Ξ fs f ≡ ⊸l+⇑P Γ₀ [] _ p Ξ fs f refl done
-- ⊸l+⇑-pos {B = I} p = refl
-- ⊸l+⇑-pos {B = B ⊗ B₁} p = refl

-- -- This could be a propositional equality.
-- ⊸l+⇑P-eq : ∀ {S Γ₀ Δ₀ Δ₁ A₀ P C Ξ}
--            (p : isPos P) (q : isPosAt C)
--            {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)}
--            (f : S ∣ Δ₀ ++ Δ₁ ⇑ C)
--            (ℓ : L S Δ₀ P) →
--            ⊸l+⇑P Γ₀ Δ₀ Δ₁ p Ξ fs f refl ℓ
--              ≗⇑ foc tt q (focl {Γ₁ = Δ₁} (pos→posat p) (⊸l+ Γ₀ Ξ (pos→posat p) fs blurl refl) (unfoc p (runLQ q ℓ f)) refl)
-- ⊸l+⇑P-eq p q (Il q₁ f) ℓ =
--   ⊸l+⇑P-eq p q f (Il-1 ℓ) • foc (focl refl (unfoc (congrunLQ ℓ (Il refl))))
-- ⊸l+⇑P-eq p q (⊗l q₁ f) ℓ = 
--   ⊸l+⇑P-eq p q f (⊗l-1 ℓ) • foc (focl refl (unfoc (congrunLQ ℓ (⊗l refl))))
-- ⊸l+⇑P-eq p q (foc s q₁ f) ℓ = foc (focl refl (unfoc (congrunLQ ℓ refl)))

-- pass⇑P-eq : {Γ : Cxt} {P C : Fma}
--             (p : isPos P) (q : isPosAt C)
--             (f : just P ∣ Γ ⇑ C) →
--             pass⇑ f ≗⇑ foc tt q (focl (pos→posat p) (pass blurl) (unfoc p f) refl)
-- pass⇑P-eq p q (Il q₁ f) = foc refl
-- pass⇑P-eq p q (⊗l q₁ f) = foc refl
-- pass⇑P-eq p q (foc s q₁ f) = ⊥-elim (pos×negat→⊥ p s)


-- ⊗r+⇑N-eq : ∀ {Γ₀} Γ₁ {Δ₀ A B₀ X Ξ}
--            (n : isNeg (Γ₁ ⊸⋆ A)) (x : isAt X)
--            (f : just X ∣ Γ₀ ++ Γ₁ ⇑ A)
--            {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → 
--            ⊗r+⇑N Γ₁ Δ₀ n Ξ f gs refl
--              ≗⇑ foc (at→negat x) (isPosAt⊗⋆ tt (fmas Ξ)) (focr (just (_ , neg→negat n)) (⊗r+ Δ₀ Ξ (neg→isn't⊗ n) blurr gs refl) (focl (at→posat x) blurl (unfoc (inj₂ n) (⊸r⋆⇑ Γ₁ f)) refl) refl)
-- ⊗r+⇑N-eq Γ₁ n x (⊸r f) =
--   ⊗r+⇑N-eq (Γ₁ ∷ʳ _) n x f • foc (focr refl (focl refl (unfoc (refl⇑ (⊸r⋆⊸r⋆⇑ Γ₁ {_ ∷ []})))))
-- ⊗r+⇑N-eq Γ₁ {X = ` X} n x (foc s q f) = foc (focr refl (~ blurl-at))

-- ⊗r+⇑N-eq' : ∀ {S Γ₀} Γ₁ {Δ₀ A B₀ Ξ}
--            (n : isNeg (Γ₁ ⊸⋆ A)) (s : isIrr S)
--            (f : S ∣ Γ₀ ++ Γ₁ ⇑ A)
--            {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → 
--            ⊗r+⇑N Γ₁ Δ₀ n Ξ f gs refl
--              ≗⇑ foc s (isPosAt⊗⋆ tt (fmas Ξ)) (focr (just (_ , neg→negat n)) (⊗r+ Δ₀ Ξ (neg→isn't⊗ n) blurr gs refl) (unfoc n (⊸r⋆⇑ Γ₁ f)) refl)
-- ⊗r+⇑N-eq' Γ₁ n s (⊸r f) = ⊗r+⇑N-eq' (Γ₁ ∷ʳ _) n s f • foc (focr refl (unfoc (refl⇑ (⊸r⋆⊸r⋆⇑ Γ₁ {_ ∷ []}))))
-- ⊗r+⇑N-eq' Γ₁ n s (foc s₁ q f) = foc refl



-- {-
-- ⇓→∙⇓ : ∀ {S Γ Γ₀ Γ₁ A Q} (q : isPosAt Q)
--   → [ ∘ , ∘ ] S ∣ Γ ⇓ Q
--   → Γ ≡ Γ₀ ++ Γ₁
--   → L S Γ₀ A
--   → [ ∙ , ∘ ] just A ∣ Γ₁ ⇓ Q

-- ⇑→∙⇓ : ∀ {S Γ Γ₀ Γ₁ A Q} (q : isPosAt Q)
--   → S ∣ Γ ⇑ Q
--   → Γ ≡ Γ₀ ++ Γ₁
--   → L S Γ₀ A
--   → [ ∙ , ∘ ] just A ∣ Γ₁ ⇓ Q

-- ⇑→∙⇓ q (Il q' f) eq ℓ = ⇑→∙⇓ q f eq (Il-1 ℓ)
-- ⇑→∙⇓ q (⊗l q' f) refl ℓ = ⇑→∙⇓ q f refl (⊗l-1 ℓ)
-- ⇑→∙⇓ q (foc s q' f) refl ℓ = ⇓→∙⇓ q f refl ℓ

-- ⇓→∙⇓ q (focl q₁ lf (focr (just (.(` _) , snd)) rf ax refl) refl) eq ℓ = {!!}
-- ⇓→∙⇓ q (focl q₁ lf (focr (just x) rf (unfoc ok f) refl) refl) eq ℓ = {!!}
-- ⇓→∙⇓ q (focl q₁ lf (unfoc ok f) refl) eq ℓ = {!!}
-- ⇓→∙⇓ q (focr s rf f eq₁) eq ℓ = {!!}
-- -}

-- focus∘emb⇑ : ∀ {S Γ A} (f : S ∣ Γ ⇑ A) → focus (emb⇑ f) ≗⇑ f
-- focus∘emb⇓ : ∀ {S Γ Q} (s : isIrr S) (q : isPosAt Q)
--   → (f : [ ∘ , ∘ ] S ∣ Γ ⇓ Q) → focus (emb⇓ f) ≗⇑ foc s q f
-- -- focus∘emb⇓ : ∀ {b c S Γ Q} (s : isIrr S) (q : isPosAt Q)
-- --   → (f : [ b , c ] S ∣ Γ ⇓ Q) → focus (emb⇓ f) ≗⇑ foc s q (no-bools⇓ s q f)
-- -- focus∘embl⇓ : ∀ {S Γ Q} (s : isIrr S) (q : isPosAt Q)
-- --   → (f : [ ∙ , ∘ ] S ∣ Γ ⇓ Q) → focus (emb⇓ f) ≗⇑ foc s q (no-bools⇓ s q f)
-- focuss∘embs⇑ : ∀ {Ξ} (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ)
--   → focuss (embs⇑ fs) ≗s⇑ fs
-- -- focus∘emblf : ∀ {S Γ₀ Γ₁ R P p s r}
-- --   → (lf : p ⇛lf S ； Γ₀)
-- --   → (f : [ ∙ , ∘ ] just P ∣ Γ₁ ⇓ R)          
-- --   → focus (emblf p lf f) ≗⇑ foc s r (focl p lf f refl)

-- focus∘emb⇑ (⊸r f) = ⊸r (focus∘emb⇑ f)
-- focus∘emb⇑ (Il q f) = refl⇑ (Il⇑eq {q = q} _) • Il (focus∘emb⇑ f)
-- focus∘emb⇑ (⊗l q f) = refl⇑ (⊗l⇑eq {q = q} _) • ⊗l (focus∘emb⇑ f)
-- focus∘emb⇑ (foc s q f) = focus∘emb⇓ s q f 

-- focuss∘embs⇑ [] = []
-- focuss∘embs⇑ (f ∷ fs) = (focus∘emb⇑ f) ∷ (focuss∘embs⇑ fs)

-- focus∘emb⇓ s q (focl q₁ (pass (⊸l+ Γ₀ Ξ q₂ fs blurl refl)) (focr (just x) (⊗r+ Δ₀ Ξ₁ m (⊗r+ Δ₁ Ξ₂ m₁ rf gs₁ eq₂) gs eq₁) f eq) refl) = ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ tt (fmas Ξ₂)) m)
-- focus∘emb⇓ s q (focl q₁ (pass (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl)) (focr (just .(` _ , _)) (⊗r+ Δ₀ Ξ₁ m blurr (g ∷ gs) refl) ax refl) refl) =
--   congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l⋆⇑ (focuss∘embs⇑ (f ∷ fs)) (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs)))))
--   • foc (focl refl (focr (⊗r+ refl (focuss∘embs⇑ (g ∷ gs))) refl))
-- focus∘emb⇓ s q (focl {Q = ` X} q₁ (pass (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl)) (focr (just (M ⊸ M₁ , tt)) (⊗r+ Δ₀ Ξ₁ m blurr (g ∷ gs) refl) (unfoc (inj₂ tt) h) refl) refl) = 
--   congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l⋆⇑ (focuss∘embs⇑ (f ∷ fs)) (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))) • cong⊗r+⇑ (focus∘emb⇑ h) (focuss∘embs⇑ (g ∷ gs)) • ⊗r+⇑N-eq [] tt tt h))
--   • foc (~ swap)
-- focus∘emb⇓ s q (focl {Q = I} q₁ (pass (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl)) (focr (just (M ⊸ M₁ , tt)) (⊗r+ Δ₀ Ξ₁ m blurr (g ∷ gs) refl) (unfoc ok h) refl) refl) = 
--   congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l⋆⇑ (focuss∘embs⇑ (f ∷ fs)) (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))) • cong⊗r+⇑ (focus∘emb⇑ h) (focuss∘embs⇑ (g ∷ gs)) ))
--   • congpass⇑ (⊸l+⇑P-eq tt (isPosAt⊗⋆ tt (fmas Ξ₁)) (⊗r+⇑N [] Δ₀ tt Ξ₁ h (g ∷ gs) refl) done)
--   • foc (focl refl (early-rf⇑N h done • focr refl (unfoc refl)))
-- focus∘emb⇓ s q (focl {Q = Q ⊗ Q₁} q₁ (pass (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl)) (focr (just (M ⊸ M₁ , tt)) (⊗r+ Δ₀ Ξ₁ m blurr (g ∷ gs) refl) (unfoc ok h) refl) refl) = 
--   congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l⋆⇑ (focuss∘embs⇑ (f ∷ fs)) (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))) • cong⊗r+⇑ (focus∘emb⇑ h) (focuss∘embs⇑ (g ∷ gs)) ))
--   • congpass⇑ (⊸l+⇑P-eq tt (isPosAt⊗⋆ tt (fmas Ξ₁)) (⊗r+⇑N [] Δ₀ tt Ξ₁ h (g ∷ gs) refl) done)
--   • foc (focl refl (early-rf⇑N h done • focr refl (unfoc refl)))
-- focus∘emb⇓ s q (focl {Q = ` Y} q₁ (pass (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl)) (focr (just (` X , tt)) (⊗r+ Δ₀ Ξ₁ m blurr (g ∷ gs) refl) (unfoc (inj₁ ()) h) refl) refl)
-- focus∘emb⇓ s q (focl {Q = I} q₁ (pass (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl)) (focr (just (` X , tt)) (⊗r+ Δ₀ Ξ₁ m blurr (g ∷ gs) refl) (unfoc (inj₁ ok) h) refl) refl) = 
--   congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l⋆⇑ (focuss∘embs⇑ (f ∷ fs)) (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))) • cong⊗r+⇑ (focus∘emb⇑ h) (focuss∘embs⇑ (g ∷ gs)) ))
--   • congpass⇑ (⊸l+⇑P-eq tt (isPosAt⊗⋆ tt (fmas Ξ₁)) (⊗r+⇑Q Δ₀ tt Ξ₁ h (g ∷ gs)) done)
--   • foc (focl refl (early-rf⇑-at tt h refl done))
-- focus∘emb⇓ s q (focl {Q = Q ⊗ Q₁} q₁ (pass (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl)) (focr (just (` X , tt)) (⊗r+ Δ₀ Ξ₁ m blurr (g ∷ gs) refl) (unfoc (inj₁ ok) h) refl) refl) = 
--   congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l⋆⇑ (focuss∘embs⇑ (f ∷ fs)) (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))) • cong⊗r+⇑ (focus∘emb⇑ h) (focuss∘embs⇑ (g ∷ gs)) ))
--   • congpass⇑ (⊸l+⇑P-eq tt (isPosAt⊗⋆ tt (fmas Ξ₁)) (⊗r+⇑Q Δ₀ tt Ξ₁ h (g ∷ gs)) done)
--   • foc (focl refl (early-rf⇑-at tt h refl done))
-- focus∘emb⇓ s q (focl q₁ (pass (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl)) (focr .(just (` _ , _)) blurr ax refl) refl) =
--   congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _)) • foc (focl (pass (⊸l+ (focuss∘embs⇑ (f ∷ fs)) refl)) refl)
-- focus∘emb⇓ s q (focl {Q = ` X} q₁ (pass (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl)) (focr .(just (_ , _)) blurr (unfoc (inj₂ ok) h) refl) refl) = ⊥-elim (neg×posat→⊥ ok q)
-- focus∘emb⇓ s q (focl {Q = I} q₁ (pass (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl)) (focr (just (` X , m)) blurr (unfoc (inj₁ tt) h) refl) refl) = 
--   congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h))
--   • congpass⇑ (⊸l+⇑P-eq tt q h done)
--   • foc (focl refl (~ blurr-at))
-- focus∘emb⇓ s q (focl {Q = Q ⊗ Q₁} q₁ (pass (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl)) (focr (just (` X , m)) blurr (unfoc (inj₁ tt) h) refl) refl) = 
--   congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h))
--   • congpass⇑ (⊸l+⇑P-eq tt q h done)
--   • foc (focl refl (~ blurr-at))
-- focus∘emb⇓ s q (focl {Q = I} q₁ (pass (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl)) (unfoc ok h) refl) = 
--   congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h))
--   • congpass⇑ (⊸l+⇑P-eq ok q h done)
-- focus∘emb⇓ s q (focl {Q = Q ⊗ Q₁} q₁ (pass (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl)) (unfoc ok h) refl) = 
--   congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h))
--   • congpass⇑ (⊸l+⇑P-eq ok q h done)
-- focus∘emb⇓ s q (focl q₁ (pass blurl) (focr (just (M , m)) (⊗r+ Δ₀ Ξ m₁ (⊗r+ Δ₁ Ξ₁ m₂ rf gs₁ eq₂) gs eq₁) f eq) refl) = ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ tt (fmas Ξ₁)) m₁)
-- focus∘emb⇓ s q (focl q₁ (pass blurl) (focr (just (.(` _) , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) ax refl) refl) =
--   congpass⇑ (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))))
--   • foc (focl refl (focr (⊗r+ refl (focuss∘embs⇑ (g ∷ gs))) refl))
-- focus∘emb⇓ s q (focl {Q = ` Y} q₁ (pass blurl) (focr (just (` X , tt)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (unfoc (inj₁ ()) f) refl) refl)
-- focus∘emb⇓ s q (focl {Q = I} q₁ (pass blurl) (focr (just (` X , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (unfoc (inj₁ ok) f) refl) refl) = 
--   congpass⇑ (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))) • cong⊗r+⇑ (focus∘emb⇑ f) (focuss∘embs⇑ (g ∷ gs)))
--   • pass⇑P-eq ok (isPosAt⊗⋆ tt (fmas Ξ)) (⊗r+⇑Q Δ₀ tt Ξ f (g ∷ gs))
--   • foc (focl refl (early-rf⇑-at tt f refl done))
-- focus∘emb⇓ s q (focl {Q = _ ⊗ _} q₁ (pass blurl) (focr (just (` X , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (unfoc (inj₁ ok) f) refl) refl) = 
--   congpass⇑ (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))) • cong⊗r+⇑ (focus∘emb⇑ f) (focuss∘embs⇑ (g ∷ gs)))
--   • pass⇑P-eq ok (isPosAt⊗⋆ tt (fmas Ξ)) (⊗r+⇑Q Δ₀ tt Ξ f (g ∷ gs))
--   • foc (focl refl (early-rf⇑-at tt f refl done))
-- focus∘emb⇓ s q (focl {Q = ` X} q₁ (pass blurl) (focr (just (M ⊸ M₁ , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (unfoc (inj₂ ok) f) refl) refl) = 
--   congpass⇑ (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))) • cong⊗r+⇑ (focus∘emb⇑ f) (focuss∘embs⇑ (g ∷ gs)) • ⊗r+⇑N-eq [] tt tt f)
--   • foc (~ swap)
-- focus∘emb⇓ s q (focl {Q = I} q₁ (pass blurl) (focr (just (M ⊸ M₁ , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (unfoc ok f) refl) refl) = 
--   congpass⇑ (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))) • cong⊗r+⇑ (focus∘emb⇑ f) (focuss∘embs⇑ (g ∷ gs)))
--   • pass⇑P-eq tt (isPosAt⊗⋆ tt (fmas Ξ)) (⊗r+⇑N [] Δ₀ tt Ξ f (g ∷ gs) refl)
--   • foc (focl refl (early-rf⇑N f done • focr refl (unfoc refl)))
-- focus∘emb⇓ s q (focl {Q = _ ⊗ _} q₁ (pass blurl) (focr (just (M ⊸ M₁ , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (unfoc ok f) refl) refl) = 
--   congpass⇑ (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))) • cong⊗r+⇑ (focus∘emb⇑ f) (focuss∘embs⇑ (g ∷ gs)))
--   • pass⇑P-eq tt (isPosAt⊗⋆ tt (fmas Ξ)) (⊗r+⇑N [] Δ₀ tt Ξ f (g ∷ gs) refl)
--   • foc (focl refl (early-rf⇑N f done • focr refl (unfoc refl)))
-- focus∘emb⇓ s q (focl q₁ (pass blurl) (focr (just (.(` _) , m)) blurr ax refl) refl) = refl
-- focus∘emb⇓ s q (focl {Q = I} q₁ (pass blurl) (focr (just (` X , m)) blurr (unfoc (inj₁ ok) f) refl) refl) =
--   congpass⇑ (focus∘emb⇑ f) • pass⇑P-eq ok tt f • foc (focl refl (~ blurr-at))
-- focus∘emb⇓ s q (focl {Q = _ ⊗ _} q₁ (pass blurl) (focr (just (` X , m)) blurr (unfoc (inj₁ ok) f) refl) refl) =
--   congpass⇑ (focus∘emb⇑ f) • pass⇑P-eq ok tt f • foc (focl refl (~ blurr-at))
-- focus∘emb⇓ s q (focl {Q = I} q₁ (pass blurl) (unfoc ok f) refl) = 
--   congpass⇑ (focus∘emb⇑ f) • pass⇑P-eq ok q f
-- focus∘emb⇓ s q (focl {Q = _ ⊗ _} q₁ (pass blurl) (unfoc ok f) refl) = 
--   congpass⇑ (focus∘emb⇑ f) • pass⇑P-eq ok q f

-- focus∘emb⇓ s q (focl q₁ (⊸l+ Γ₀ Ξ q₂ fs blurl refl) (focr (just x) (⊗r+ Δ₀ Ξ₁ m (⊗r+ Δ₁ Ξ₂ m₁ rf gs₁ eq₂) gs eq₁) f eq) refl) = ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ tt (fmas Ξ₂)) m)
-- focus∘emb⇓ s q (focl q₁ (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl) (focr (just .(` _ , _)) (⊗r+ Δ₀ Ξ₁ m blurr (g ∷ gs) refl) ax refl) refl) =
--   refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l⋆⇑ (focuss∘embs⇑ (f ∷ fs)) (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))))
--   • foc (focl refl (focr (⊗r+ refl (focuss∘embs⇑ (g ∷ gs))) refl))
-- focus∘emb⇓ s q (focl {Q = ` X} q₁ (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl) (focr (just (M ⊸ M₁ , tt)) (⊗r+ Δ₀ Ξ₁ m blurr (g ∷ gs) refl) (unfoc (inj₂ tt) h) refl) refl) = 
--   refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l⋆⇑ (focuss∘embs⇑ (f ∷ fs)) (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))) • cong⊗r+⇑ (focus∘emb⇑ h) (focuss∘embs⇑ (g ∷ gs)) • ⊗r+⇑N-eq [] tt tt h)
--   • foc (~ swap)
-- focus∘emb⇓ s q (focl {Q = I} q₁ (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl) (focr (just (M ⊸ M₁ , tt)) (⊗r+ Δ₀ Ξ₁ m blurr (g ∷ gs) refl) (unfoc ok h) refl) refl) = 
--   refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l⋆⇑ (focuss∘embs⇑ (f ∷ fs)) (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))) • cong⊗r+⇑ (focus∘emb⇑ h) (focuss∘embs⇑ (g ∷ gs)))
--   • ⊸l+⇑P-eq tt (isPosAt⊗⋆ tt (fmas Ξ₁)) (⊗r+⇑N [] Δ₀ tt Ξ₁ h (g ∷ gs) refl) done
--   • foc (focl refl (early-rf⇑N h done • focr refl (unfoc refl)))
-- focus∘emb⇓ s q (focl {Q = Q ⊗ Q₁} q₁ (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl) (focr (just (M ⊸ M₁ , tt)) (⊗r+ Δ₀ Ξ₁ m blurr (g ∷ gs) refl) (unfoc ok h) refl) refl) = 
--   refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l⋆⇑ (focuss∘embs⇑ (f ∷ fs)) (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))) • cong⊗r+⇑ (focus∘emb⇑ h) (focuss∘embs⇑ (g ∷ gs)))
--   • ⊸l+⇑P-eq tt (isPosAt⊗⋆ tt (fmas Ξ₁)) (⊗r+⇑N [] Δ₀ tt Ξ₁ h (g ∷ gs) refl) done
--   • foc (focl refl (early-rf⇑N h done • focr refl (unfoc refl)))
-- focus∘emb⇓ s q (focl {Q = ` Y} q₁ (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl) (focr (just (` X , tt)) (⊗r+ Δ₀ Ξ₁ m blurr (g ∷ gs) refl) (unfoc (inj₁ ()) h) refl) refl)
-- focus∘emb⇓ s q (focl {Q = I} q₁ (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl) (focr (just (` X , tt)) (⊗r+ Δ₀ Ξ₁ m blurr (g ∷ gs) refl) (unfoc (inj₁ ok) h) refl) refl) = 
--   refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l⋆⇑ (focuss∘embs⇑ (f ∷ fs)) (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))) • cong⊗r+⇑ (focus∘emb⇑ h) (focuss∘embs⇑ (g ∷ gs)))
--   • ⊸l+⇑P-eq tt (isPosAt⊗⋆ tt (fmas Ξ₁)) (⊗r+⇑Q Δ₀ tt Ξ₁ h (g ∷ gs)) done
--   • foc (focl refl (early-rf⇑-at tt h refl done))
-- focus∘emb⇓ s q (focl {Q = Q ⊗ Q₁} q₁ (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl) (focr (just (` X , tt)) (⊗r+ Δ₀ Ξ₁ m blurr (g ∷ gs) refl) (unfoc (inj₁ ok) h) refl) refl) = 
--   refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l⋆⇑ (focuss∘embs⇑ (f ∷ fs)) (refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))) • cong⊗r+⇑ (focus∘emb⇑ h) (focuss∘embs⇑ (g ∷ gs)))
--   • ⊸l+⇑P-eq tt (isPosAt⊗⋆ tt (fmas Ξ₁)) (⊗r+⇑Q Δ₀ tt Ξ₁ h (g ∷ gs)) done
--   • foc (focl refl (early-rf⇑-at tt h refl done))
-- focus∘emb⇓ s q (focl q₁ (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl) (focr .(just (` _ , _)) blurr ax refl) refl) =
--   refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • foc (focl (⊸l+ (focuss∘embs⇑ (f ∷ fs)) refl) refl)
-- focus∘emb⇓ s q (focl {Q = ` X} q₁ (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl) (focr .(just (_ , _)) blurr (unfoc (inj₂ ok) h) refl) refl) = ⊥-elim (neg×posat→⊥ ok q)
-- focus∘emb⇓ s q (focl {Q = I} q₁ (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl) (focr (just (` X , m)) blurr (unfoc (inj₁ tt) h) refl) refl) = 
--   refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h)
--   • ⊸l+⇑P-eq tt q h done
--   • foc (focl refl (~ blurr-at))
-- focus∘emb⇓ s q (focl {Q = Q ⊗ Q₁} q₁ (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl) (focr (just (` X , m)) blurr (unfoc (inj₁ tt) h) refl) refl) = 
--   refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h)
--   • ⊸l+⇑P-eq tt q h done
--   • foc (focl refl (~ blurr-at))
-- focus∘emb⇓ s q (focl {Q = I} q₁ (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl) (unfoc ok h) refl) = 
--   refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h)
--   • ⊸l+⇑P-eq ok q h done
-- focus∘emb⇓ s q (focl {Q = Q ⊗ Q₁} q₁ (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl) (unfoc ok h) refl) = 
--   refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h)
--   • ⊸l+⇑P-eq ok q h done


-- focus∘emb⇓ s q (focl {Q = ` X} q₁ blurl (focr (just (_ , m)) (⊗r+ Δ₀ Ξ m₁ (⊗r+ Δ₁ Ξ₁ m₂ rf gs₁ eq) gs refl) f refl) refl) = ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ tt (fmas Ξ₁)) m₁)
-- focus∘emb⇓ s q (focl {Q = ` X} q₁ blurl (focr (just (.(` X) , tt)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) ax refl) refl) =
--   refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs))) • foc (focl refl (focr (⊗r+ refl (focuss∘embs⇑ (g ∷ gs))) refl))
-- focus∘emb⇓ s q (focl {Q = ` X} q₁ blurl (focr (just (M ⊸ M' , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (unfoc (inj₂ n) f) refl) refl) = 
--   refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (focus∘emb⇑ f) (focuss∘embs⇑ (g ∷ gs))
--   • ⊗r+⇑N-eq [] n tt f
--   • foc (~ swap)
-- focus∘emb⇓ s q (focl {Q = ` X} q₁ blurl (focr (just (` .X , tt)) blurr ax refl) refl) = refl
-- focus∘emb⇓ s q (focl {Q = ` X} q₁ blurl (focr (just (` Y , tt)) blurr (unfoc (inj₁ ()) f) refl) refl)
-- focus∘emb⇓ s q (focl {Q = ` X} q₁ blurl (focr (just (` Y , tt)) blurr (unfoc (inj₂ ()) f) refl) refl)

-- focus∘emb⇓ s q (focr (just (M , m)) (⊗r+ Δ₀ Ξ m₁ (⊗r+ Δ₁ Ξ₁ m₂ rf gs₁ eq₁) gs eq) f refl) = ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ tt (fmas Ξ₁)) m₁)
-- focus∘emb⇓ s q (focr (just (.(` _) , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl q₁ (pass (⊸l+ Γ₀ Ξ₁ q₂ (f ∷ fs) blurl refl)) ax refl) refl) =
--   refl⇑ (focus⊗r⋆ (pass (⊸l⋆ (embs⇑ (f ∷ fs)) ax)) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) ax))) (focuss∘embs⇑ (g ∷ gs))
--   • foc (swap • focr refl (focl (pass (⊸l+ (focuss∘embs⇑ (f ∷ fs)) refl)) refl))
-- focus∘emb⇓ s q (focr (just (` X , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q =  ` Y} q₁ (pass (⊸l+ Γ₀ Ξ₁ q₂ (f ∷ fs) blurl refl)) (unfoc (inj₂ ()) h) refl) refl) 
-- focus∘emb⇓ s q (focr (just (` X , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q =  I} q₁ (pass (⊸l+ Γ₀ Ξ₁ q₂ (f ∷ fs) blurl refl)) (unfoc (inj₁ tt) h) refl) refl) =
--   refl⇑ (focus⊗r⋆ (pass (⊸l⋆ (embs⇑ (f ∷ fs)) _)) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h) • ⊸l+⇑P-eq tt tt h done)) (focuss∘embs⇑ (g ∷ gs))
--   • foc (focl refl (early-rf⇑-at tt h refl done) • swap)
-- focus∘emb⇓ s q (focr (just (` X , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q =  _ ⊗ _} q₁ (pass (⊸l+ Γ₀ Ξ₁ q₂ (f ∷ fs) blurl refl)) (unfoc (inj₁ tt)h) refl) refl) =
--   refl⇑ (focus⊗r⋆ (pass (⊸l⋆ (embs⇑ (f ∷ fs)) _)) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h) • ⊸l+⇑P-eq tt tt h done)) (focuss∘embs⇑ (g ∷ gs))
--   • foc (focl refl (early-rf⇑-at tt h refl done) • swap)
-- focus∘emb⇓ s q (focr (just (M ⊸ M' , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q = ` X} q₁ (pass (⊸l+ Γ₀ Ξ₁ q₂ (f ∷ fs) blurl refl)) (unfoc (inj₂ ok) h) refl) refl) =
--   refl⇑ (focus⊗r⋆ (pass (⊸l⋆ (embs⇑ (f ∷ fs)) _)) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h))) (focuss∘embs⇑ (g ∷ gs))
--   • ⊗r+pass⇑ {f = ⊸l+⇑M Γ₀ tt Ξ₁ (f ∷ fs) h}
--   • congpass⇑ (⊗r+⊸l+⇑ {h = h} • cong⊸l+⇑M₂ (⊗r+⇑N-eq [] ok tt h))
--   • foc refl
-- focus∘emb⇓ s q (focr (just (M ⊸ M' , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q = I} q₁ (pass (⊸l+ Γ₀ Ξ₁ q₂ (f ∷ fs) blurl refl)) (unfoc ok h) refl) refl) =
--   refl⇑ (focus⊗r⋆ (pass (⊸l⋆ (embs⇑ (f ∷ fs)) _)) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h))) (focuss∘embs⇑ (g ∷ gs))
--   • ⊗r+pass⇑ {f = ⊸l+⇑P Γ₀ [] _ tt Ξ₁ (f ∷ fs) h refl done}
--   • congpass⇑ (⊗r+⊸l+⇑ {h = h})
--   • congpass⇑ (⊸l+⇑P-eq tt (isPosAt⊗⋆ tt (fmas Ξ)) (⊗r+⇑N [] Δ₀ tt Ξ h (g ∷ gs) refl) done)
--   • foc (focl refl (early-rf⇑N h done • focr refl (unfoc refl)) • swap)
-- focus∘emb⇓ s q (focr (just (M ⊸ M' , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q = _ ⊗ _} q₁ (pass (⊸l+ Γ₀ Ξ₁ q₂ (f ∷ fs) blurl refl)) (unfoc ok h) refl) refl) =
--   refl⇑ (focus⊗r⋆ (pass (⊸l⋆ (embs⇑ (f ∷ fs)) _)) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h))) (focuss∘embs⇑ (g ∷ gs))
--   • ⊗r+pass⇑ {f = ⊸l+⇑P Γ₀ [] _ tt Ξ₁ (f ∷ fs) h refl done}
--   • congpass⇑ (⊗r+⊸l+⇑ {h = h})
--   • congpass⇑ (⊸l+⇑P-eq tt (isPosAt⊗⋆ tt (fmas Ξ)) (⊗r+⇑N [] Δ₀ tt Ξ h (g ∷ gs) refl) done)
--   • foc (focl refl (early-rf⇑N h done • focr refl (unfoc refl)) • swap)

-- focus∘emb⇓ s q (focr (just (.(` _) , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl q₁ (pass blurl) ax refl) refl) =
--   refl⇑ (focus⊗r⋆ (pass ax) (embs⇑ (g ∷ gs)))
--   • foc (focl refl (focr (⊗r+ refl (focuss∘embs⇑ (g ∷ gs))) refl) • swap)
-- focus∘emb⇓ s q (focr (just (` X , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q = I} q₁ (pass blurl) (unfoc (inj₁ ok) f) refl) refl) = 
--   refl⇑ (focus⊗r⋆ (pass _) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (congpass⇑ (focus∘emb⇑ f) • pass⇑P-eq ok tt f) (focuss∘embs⇑ (g ∷ gs))
--   • foc (focl refl (early-rf⇑-at tt f refl done) • swap)
-- focus∘emb⇓ s q (focr (just (` X , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q = _ ⊗ _} q₁ (pass blurl) (unfoc (inj₁ ok) f) refl) refl) = 
--   refl⇑ (focus⊗r⋆ (pass _) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (congpass⇑ (focus∘emb⇑ f) • pass⇑P-eq ok tt f) (focuss∘embs⇑ (g ∷ gs))
--   • foc (focl refl (early-rf⇑-at tt f refl done) • swap)
-- focus∘emb⇓ s q (focr (just (M ⊸ M' , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q = ` X} q₁ (pass blurl) (unfoc ok f) refl) refl) = 
--   refl⇑ (focus⊗r⋆ (pass _) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (congpass⇑ (focus∘emb⇑ f)) (focuss∘embs⇑ (g ∷ gs))
--   • ⊗r+⇑N-eq' [] tt tt (pass⇑ f)
--   • foc (focr refl (early-pass⇑-at [] tt f • focl refl (unfoc refl)))
-- focus∘emb⇓ s q (focr (just (M ⊸ M' , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q = I} q₁ (pass blurl) (unfoc ok f) refl) refl) = 
--   refl⇑ (focus⊗r⋆ (pass _) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (congpass⇑ (focus∘emb⇑ f)) (focuss∘embs⇑ (g ∷ gs))
--   • ⊗r+pass⇑ {f = f}
--   • pass⇑P-eq tt (isPosAt⊗⋆ tt (fmas Ξ)) _
--   • foc (focl refl (early-rf⇑N f done • focr refl (unfoc refl)) • swap)
-- focus∘emb⇓ s q (focr (just (M ⊸ M' , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q = _ ⊗ _} q₁ (pass blurl) (unfoc ok f) refl) refl) = 
--   refl⇑ (focus⊗r⋆ (pass _) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (congpass⇑ (focus∘emb⇑ f)) (focuss∘embs⇑ (g ∷ gs))
--   • ⊗r+pass⇑ {f = f}
--   • pass⇑P-eq tt (isPosAt⊗⋆ tt (fmas Ξ)) _
--   • foc (focl refl (early-rf⇑N f done • focr refl (unfoc refl)) • swap)

-- focus∘emb⇓ s q (focr (just (.(` _) , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl q₁ (⊸l+ Γ₀ Ξ₁ q₂ (f ∷ fs) blurl refl) ax refl) refl) =
--   refl⇑ (focus⊗r⋆ (⊸l⋆ (embs⇑ (f ∷ fs)) ax) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) ax)) (focuss∘embs⇑ (g ∷ gs))
--   • foc (swap • focr refl (focl (⊸l+ (focuss∘embs⇑ (f ∷ fs)) refl) refl))
-- focus∘emb⇓ s q (focr (just (` X , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q =  ` Y} q₁ (⊸l+ Γ₀ Ξ₁ q₂ (f ∷ fs) blurl refl) (unfoc (inj₂ ()) h) refl) refl) 
-- focus∘emb⇓ s q (focr (just (` X , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q =  I} q₁ (⊸l+ Γ₀ Ξ₁ q₂ (f ∷ fs) blurl refl) (unfoc (inj₁ tt) h) refl) refl) =
--   refl⇑ (focus⊗r⋆ (⊸l⋆ (embs⇑ (f ∷ fs)) _) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h) • ⊸l+⇑P-eq tt tt h done) (focuss∘embs⇑ (g ∷ gs))
--   • foc (focl refl (early-rf⇑-at tt h refl done) • swap)
-- focus∘emb⇓ s q (focr (just (` X , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q =  _ ⊗ _} q₁ (⊸l+ Γ₀ Ξ₁ q₂ (f ∷ fs) blurl refl) (unfoc (inj₁ tt)h) refl) refl) =
--   refl⇑ (focus⊗r⋆ (⊸l⋆ (embs⇑ (f ∷ fs)) _) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h) • ⊸l+⇑P-eq tt tt h done) (focuss∘embs⇑ (g ∷ gs))
--   • foc (focl refl (early-rf⇑-at tt h refl done) • swap)
-- focus∘emb⇓ s q (focr (just (M ⊸ M' , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q = ` X} q₁ (⊸l+ Γ₀ Ξ₁ q₂ (f ∷ fs) blurl refl) (unfoc (inj₂ ok) h) refl) refl) =
--   refl⇑ (focus⊗r⋆ (⊸l⋆ (embs⇑ (f ∷ fs)) _) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h)) (focuss∘embs⇑ (g ∷ gs))
--   • ⊗r+⊸l+⇑ {h = h} • cong⊸l+⇑M₂ (⊗r+⇑N-eq [] ok tt h)
--   • foc refl
-- focus∘emb⇓ s q (focr (just (M ⊸ M' , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q = I} q₁ (⊸l+ Γ₀ Ξ₁ q₂ (f ∷ fs) blurl refl) (unfoc ok h) refl) refl) =
--   refl⇑ (focus⊗r⋆ (⊸l⋆ (embs⇑ (f ∷ fs)) _) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h)) (focuss∘embs⇑ (g ∷ gs))
--   • ⊗r+⊸l+⇑ {h = h}
--   • ⊸l+⇑P-eq tt (isPosAt⊗⋆ tt (fmas Ξ)) (⊗r+⇑N [] Δ₀ tt Ξ h (g ∷ gs) refl) done
--   • foc (focl refl (early-rf⇑N h done • focr refl (unfoc refl)) • swap)
-- focus∘emb⇓ s q (focr (just (M ⊸ M' , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q = _ ⊗ _} q₁ (⊸l+ Γ₀ Ξ₁ q₂ (f ∷ fs) blurl refl) (unfoc ok h) refl) refl) =
--   refl⇑ (focus⊗r⋆ (⊸l⋆ (embs⇑ (f ∷ fs)) _) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h)) (focuss∘embs⇑ (g ∷ gs))
--   • ⊗r+⊸l+⇑ {h = h}
--   • ⊸l+⇑P-eq tt (isPosAt⊗⋆ tt (fmas Ξ)) (⊗r+⇑N [] Δ₀ tt Ξ h (g ∷ gs) refl) done
--   • foc (focl refl (early-rf⇑N h done • focr refl (unfoc refl)) • swap)

-- focus∘emb⇓ s q (focr (just (.(` _) , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl q₁ blurl ax refl) refl) =
--   refl⇑ (focus⊗r⋆ ax (embs⇑ (g ∷ gs)))
--   • foc (focl refl (focr (⊗r+ refl (focuss∘embs⇑ (g ∷ gs))) refl) • swap)
-- focus∘emb⇓ s q (focr (just (M ⊸ M' , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (focl {Q = ` X} q₁ blurl (unfoc (inj₂ ok) f) refl) refl) = 
--   refl⇑ (focus⊗r⋆ (emb⇑ f) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (focus∘emb⇑ f) (focuss∘embs⇑ (g ∷ gs))
--   • ⊗r+⇑N-eq [] tt tt f
--   • foc refl
-- focus∘emb⇓ s q (focr (just (M ⊸ M' , m)) (⊗r+ Δ₀ Ξ m₁ blurr (g ∷ gs) refl) (unfoc ok f) refl) = 
--   refl⇑ (focus⊗r⋆ (emb⇑ f) (embs⇑ (g ∷ gs)))
--   • cong⊗r+⇑ (focus∘emb⇑ f) (focuss∘embs⇑ (g ∷ gs))
--   • ⊗r+⇑N-eq' [] tt s f
--   • foc refl
-- focus∘emb⇓ s q (focr (just (.(` _) , m)) blurr (focl q₁ (pass (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl)) ax refl) refl) =
--   congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _)) • foc (focl (pass (⊸l+ (focuss∘embs⇑ (f ∷ fs)) refl)) refl • swap)
-- focus∘emb⇓ s q (focr (just (.(` _) , m)) blurr (focl q₁ (pass blurl) ax refl) refl) = foc swap
-- focus∘emb⇓ s q (focr (just (.(` _) , m)) blurr (focl q₁ (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl) ax refl) refl) =
--   refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • foc (focl (⊸l+ (focuss∘embs⇑ (f ∷ fs)) refl) refl • swap)
-- focus∘emb⇓ s q (focr (just (.(` _) , m)) blurr (focl q₁ blurl ax refl) refl) = foc swap
-- focus∘emb⇓ s q (focr (just (` X , tt)) blurr (focl {Q = I} q₁ (pass (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl)) (unfoc (inj₁ ok) h) refl) refl) =
--   congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h))
--   • congpass⇑ (⊸l+⇑P-eq tt q h done)
--   • foc (focl refl (~ blurr-at) • swap)
-- focus∘emb⇓ s q (focr (just (` X , tt)) blurr (focl {Q = Q ⊗ Q₁} q₁ (pass (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl)) (unfoc (inj₁ ok) h) refl) refl) = 
--   congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h))
--   • congpass⇑ (⊸l+⇑P-eq tt q h done)
--   • foc (focl refl (~ blurr-at) • swap)
-- focus∘emb⇓ s q (focr (just (` X , tt)) blurr (focl {Q = I} q₁ (pass blurl) (unfoc (inj₁ ok) f) refl) refl) =
--   congpass⇑ (focus∘emb⇑ f) • pass⇑P-eq ok tt f • foc (focl refl (~ blurr-at) • swap)
-- focus∘emb⇓ s q (focr (just (` X , tt)) blurr (focl {Q = Q ⊗ Q₁} q₁ (pass blurl) (unfoc (inj₁ ok) f) refl) refl) = 
--   congpass⇑ (focus∘emb⇑ f) • pass⇑P-eq ok tt f • foc (focl refl (~ blurr-at) • swap)
-- focus∘emb⇓ s q (focr (just (` X , tt)) blurr (focl {Q = I} q₁ (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl) (unfoc (inj₁ ok) h) refl) refl) =
--   refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h)
--   • ⊸l+⇑P-eq tt q h done
--   • foc (focl refl (~ blurr-at) • swap)
-- focus∘emb⇓ s q (focr (just (` X , tt)) blurr (focl {Q = Q ⊗ Q₁} q₁ (⊸l+ Γ₀ Ξ q₂ (f ∷ fs) blurl refl) (unfoc (inj₁ ok) h) refl) refl) = 
--   refl⇑ (focus⊸l⋆ (embs⇑ (f ∷ fs)) _) • cong⊸l+⇑ (focuss∘embs⇑ (f ∷ fs)) (focus∘emb⇑ h)
--   • ⊸l+⇑P-eq tt q h done
--   • foc (focl refl (~ blurr-at) • swap)
-- focus∘emb⇓ s q (focr (just (` X , tt)) blurr (focl {Q = ` x} q₁ blurl (unfoc (inj₂ ()) f) refl) refl)
-- focus∘emb⇓ s q (focr (just (` X , tt)) blurr (unfoc () f) refl)
-- focus∘emb⇓ s q (focr ─ Ir (refl , refl) refl) = refl
-- focus∘emb⇓ s q (focr ─ (⊗r+ Δ₀ Ξ m Ir (g ∷ gs) refl) (refl , refl) refl) = 
--   refl⇑ (focus⊗r⋆ _ (embs⇑ (g ∷ gs)))
--   • foc (focrn (⊗r+ refl (focuss∘embs⇑ (g ∷ gs))))
-- focus∘emb⇓ s q (focr ─ (⊗r+ Δ₀ Ξ m (⊗r+ Δ₁ Ξ₁ m₁ rf gs₁ eq₁) gs eq) (refl , refl) refl) = ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ tt (fmas Ξ₁)) m)





-- -- focus∘emb⇓ {∘} {∙} s q (unfoc ok f) = ⊥-elim (neg×posat→⊥ ok q)
-- -- focus∘emb⇓ {∙} {∘} {just x} s q (unfoc ok f) = ⊥-elim (pos×negat→⊥ ok s)
-- -- focus∘emb⇓ {∙} {∙} {just x} s q (unfoc (inj₁ ok) f) = ⊥-elim (pos×negat→⊥ ok s)
-- -- focus∘emb⇓ {∙} {∙} {just x} s q (unfoc (inj₂ ok) f) = ⊥-elim (neg×posat→⊥ ok q)

-- -- focus∘emblf (pass (⊸l+ Γ₀ Ξ q fs blurl refl)) (focr (just (.(` _) , snd)) rf ax refl) = {!!}
-- -- focus∘emblf {P = ` X} (pass (⊸l+ Γ₀ Ξ q fs blurl refl)) (focr (just (N , _)) (⊗r+ Δ₀ Ξ₁ m (⊗r+ Δ₁ Ξ₂ m₁ rf gs₁ eq₁) gs eq) (unfoc (inj₂ n) f) refl) = {!imp!}
-- -- focus∘emblf {P = ` X} (pass (⊸l+ Γ₀ Ξ q fs blurl refl)) (focr (just (N , _)) (⊗r+ Δ₀ Ξ₁ m blurr gs refl) (unfoc (inj₂ n) f) refl) =
-- -- --  congpass⇑ (refl⇑ (focus⊸l⋆ (embs⇑ fs) _) • cong⊸l⋆⇑ (focuss∘embs⇑ fs) {!!}) • {!!}
-- -- {!!}
-- -- focus∘emblf {P = ` X} (pass (⊸l+ Γ₀ Ξ q fs blurl refl)) (focr (just (N , _)) blurr (unfoc (inj₂ n) f) refl) = {!!}
-- -- focus∘emblf {P = I} (pass (⊸l+ Γ₀ Ξ q fs blurl refl)) (focr (just x) rf (unfoc ok f) refl) = {!!}
-- -- focus∘emblf {P = P ⊗ P₁} (pass (⊸l+ Γ₀ Ξ q fs blurl refl)) (focr (just x) rf (unfoc ok f) refl) = {!!}
-- -- focus∘emblf (pass (⊸l+ Γ₀ Ξ q fs blurl refl)) (unfoc ok f) = {!!}
-- -- focus∘emblf (pass blurl) f = {!!}
-- -- focus∘emblf (⊸l+ Γ₀ Ξ q fs lf eq) f = {!!}
-- -- focus∘emblf blurl f = {!!}


-- -- focus∘emb⇓ s q (focl q₁ (pass (⊸l+ Γ₀ Ξ q₂ fs blurl refl)) f refl) = {!fs!}
-- -- focus∘emb⇓ s q (focl q₁ (pass blurl) (focr s₁ (⊗r+ Δ₀ Ξ m (⊗r+ Δ₁ Ξ₁ m₁ rf gs₁ eq₂) gs eq₁) f eq) refl) = ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ _ (fmas Ξ₁)) m)
-- -- focus∘emb⇓ s q (focl q₁ (pass blurl) (focr .(just (` _ , _)) (⊗r+ Δ₀ Ξ m blurr gs refl) ax refl) refl) = {!swapped!}
-- -- focus∘emb⇓ s q (focl q₁ (pass blurl) (focr .(just (_ , _)) (⊗r+ Δ₀ Ξ m blurr gs refl) (unfoc ok f) refl) refl) = {!swapped!}
-- -- focus∘emb⇓ s q (focl q₁ (pass blurl) (focr .(just (` _ , _)) blurr ax refl) refl) =
-- --   foc (focl refl (~ {!!}))
-- -- focus∘emb⇓ s q (focl q₁ (pass blurl) (focr .(just (_ , _)) blurr (unfoc ok f) refl) refl) = {!!}
-- -- focus∘emb⇓ s q (focl q₁ (pass blurl) (unfoc ok f) refl) = {!!}
-- -- focus∘emb⇓ s q (focl q₁ (⊸l+ Γ₀ Ξ q₂ fs blurl refl) f refl) = {!!}
-- -- focus∘emb⇓ s q (focl q₁ blurl f refl) = {!!}
-- -- focus∘emb⇓ s q (focr (just _) (⊗r+ Δ₀ Ξ m (⊗r+ Δ₁ Ξ₁ m₁ rf gs₁ eq₂) gs eq₁) f eq) =
-- --   ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ tt (fmas Ξ₁)) m)
-- -- focus∘emb⇓ s q (focr (just _) (⊗r+ Δ₀ Ξ m blurr gs refl) f refl) = {!!}
-- -- focus∘emb⇓ s q (focr (just _) blurr (focl q₁ lf f eq) refl) = {!!}
-- -- focus∘emb⇓ s q (focr (just _) blurr (unfoc ok f) refl) = {!imp!}
-- -- focus∘emb⇓ s q (focr ─ Ir (refl , refl) refl) = refl
-- -- focus∘emb⇓ s q (focr ─ (⊗r+ Δ₀ Ξ m Ir gs refl) (refl , refl) refl) = {!!}
-- -- focus∘emb⇓ s q (focr ─ (⊗r+ Δ₀ Ξ m (⊗r+ Δ₁ Ξ₁ m₁ rf gs₁ eq₂) gs eq₁) f eq) =
-- --   ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ tt (fmas Ξ₁)) m)
