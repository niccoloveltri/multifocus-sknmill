{-# OPTIONS --rewriting #-}

module correct.max-multifocus.Iso2 where

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
open import MultifocSeqCalc as MF
open import MaxMultifocSeqCalc as MMF
open import correct.multifocus.EqComplete as EqC
open import correct.max-multifocus.Lemmata as Lem

untag-untag-seq-f : {b b' : Tag} {S : Stp} {Γ : TCxt} {A : Fma}
        (f : MMF.[ b , b' ] (∘ , S) ∣ Γ ⇓ (∘ , A)) →
        untag⇓ (untag-seq-f f) ≡ untag⇓ f
untag-untag-seq-f ax = refl
untag-untag-seq-f (focl q lf f refl refl ξ) =
  cong (λ x → focl q (untag-lf lf) x refl) (untag-untag-seq-f f)
untag-untag-seq-f (focr (just x) rf f refl refl ξ) =
  cong (λ y → focr (just x) (untag-rf rf) y refl) (untag-untag-seq-f f)
untag-untag-seq-f (focr ─ rf (refl , refl) refl refl ξ) = refl
untag-untag-seq-f (unfoc ok f) = refl

untag-l∙→∘⇑ : ∀ {S Γ C} (f : (∙ , S) MMF.∣ Γ ⇑ (∘ , C))
  → untag⇑ (l∙→∘⇑ f) ≡ untag⇑ f
untag-l∙→∘⇑ (⊸r f) = cong ⊸r (untag-l∙→∘⇑ f)
untag-l∙→∘⇑ (foc s q (focl q₁ lf f refl refl ξ)) =
  cong (foc s q) (cong (λ x → focl q₁ (untag-lf lf) x refl) (untag-untag-seq-f f))
untag-l∙→∘⇑ (foc s q (focr (just x) rf (unfoc ok f) refl refl ξ)) = refl
untag-l∙→∘⇑ (foc s q (focr ─ rf (refl , refl) refl refl ξ)) = refl


untag-Il⇑ : {r : Tag} {Γ : TCxt} {C : Fma}
     (f :  (∘ , ─) MMF.∣ Γ ⇑ (r , C)) →
  -------------------------
     untag⇑ (MMF.Il⇑ f) ≡ MF.Il⇑ (untag⇑ f)
untag-Il⇑ (⊸r f) = cong ⊸r (untag-Il⇑ f)
untag-Il⇑ (foc s q f) = refl

untag-⊗l⇑ : {r : Tag} {Γ : TCxt} {A B C : Fma}
     (f : (∘ , just A) MMF.∣ (r , B) ∷ Γ ⇑ (r , C)) →
  -------------------------------------
       untag⇑ (MMF.⊗l⇑ f) ≡ MF.⊗l⇑ (untag⇑ f)
untag-⊗l⇑ (⊸r f) = cong ⊸r (untag-⊗l⇑ f)
untag-⊗l⇑ (Il q f) = refl
untag-⊗l⇑ (⊗l q f) = cong (⊗l q) (trans (untag-⊗l⇑ f) (EqC.⊗l⇑eq _))
untag-⊗l⇑ (foc s q f) = refl

untag-runL : ∀ {r S Γ Δ A C} (ℓ : MF.L S Γ A) (f : (∘ , S) MMF.∣ tag-cxt r Γ ++ Δ ⇑ (r , C))
  → untag⇑ {Γ = Δ} (MMF.runL ℓ f) ≡ MF.runL ℓ (untag⇑ {Γ = tag-cxt r Γ ++ Δ} f) 
untag-runL done f = refl
untag-runL (Il-1 ℓ) f = trans (untag-runL ℓ (MMF.Il⇑ f)) (cong (MF.runL ℓ) (untag-Il⇑ f))
untag-runL (⊗l-1 ℓ) f = trans (untag-runL ℓ (MMF.⊗l⇑ f)) (cong (MF.runL ℓ) (untag-⊗l⇑ f))

-- MF-only-lfP : {S : Stp} {Δ₀ : Cxt} (Δ₁ : TCxt) {P C : Fma}
--                (s : isIrr S) (p : isPos P) 
--                (lf : pos→posat p ⇛lf S ∣ Δ₀) 
--                (f : (∘ , just P) MMF.∣ Δ₁ ⇑ (∘ , C)) → S MF.∣ Δ₀ ++ untag-cxt Δ₁ ⇑ C
-- MF-only-lfP Δ₁ s p lf (⊸r f) = ⊸r (MF-only-lfP (Δ₁ ∷ʳ _) s p lf f)
-- MF-only-lfP Δ₁ s p lf (Il q f) = foc s q (focl {Γ₁ = untag-cxt Δ₁} _ (untag-lf lf) (unfoc p (Il q (untag⇑ f))) refl)
-- MF-only-lfP Δ₁ s p lf (⊗l q f) = foc s q (focl {Γ₁ = untag-cxt Δ₁} _ (untag-lf lf) (unfoc p (⊗l q (untag⇑ f))) refl)
-- MF-only-lfP Δ₁ s p lf (foc m q f) = foc s q (focl {Γ₁ = untag-cxt Δ₁} _ (untag-lf lf) (unfoc p (foc m q (untag⇓ f))) refl)

MF-only-lfP : {S S' : Stp} {Γ Δ₀ : Cxt} (Δ₁ : Cxt) {P C : Fma}
               (s : isIrr S) (p : isPos P) 
               (lf : pos→posat p ⇛lf S ； Δ₀) 
               (f : S' MF.∣ Γ ++ Δ₁ ⇑ C)
               (ℓ : MF.L S' Γ P) →
               S MF.∣ Δ₀ ++ Δ₁ ⇑ C
MF-only-lfP Δ₁ s p lf (⊸r f) ℓ = ⊸r (MF-only-lfP (Δ₁ ∷ʳ _) s p lf f ℓ)
MF-only-lfP Δ₁ s p lf (Il q f) ℓ = foc s q (focl {Γ₁ = Δ₁} _ lf (unfoc p (MF.runL ℓ (Il q f))) refl)
MF-only-lfP Δ₁ s p lf (⊗l q f) ℓ = foc s q (focl {Γ₁ = Δ₁} _ lf (unfoc p (MF.runL ℓ (⊗l q f))) refl)
MF-only-lfP Δ₁ s p lf (foc m q f) ℓ = foc s q (focl {Γ₁ = Δ₁} _ lf (unfoc p (MF.runL ℓ (foc m q f))) refl)

MF-only-lfP-eq : {S S' : Stp} {Γ Δ₀ : Cxt} (Δ₁ : Cxt) {P Q : Fma}
                 (s : isIrr S) (p : isPos P) (q : isPosAt Q) 
                 (lf : pos→posat p ⇛lf S ； Δ₀) 
                 (f : S' MF.∣ Γ ++ Δ₁ ⇑ Q)
                 (ℓ : MF.L S' Γ P) →
                 MF-only-lfP Δ₁ s p lf f ℓ ≡ foc s q (focl {Γ₁ = Δ₁} _ lf (unfoc p (MF.runL ℓ f)) refl)
MF-only-lfP-eq Δ₁ s p q lf (Il q₁ f) ℓ rewrite isProp-isPosAt q q₁ = refl
MF-only-lfP-eq Δ₁ s p q lf (⊗l q₁ f) ℓ rewrite isProp-isPosAt q q₁ = refl
MF-only-lfP-eq Δ₁ s p q lf (foc s₁ q₁ f) ℓ rewrite isProp-isPosAt q q₁ = refl

-- MF-only-lfP' : {S S' : Stp} {Γ Δ₀ : Cxt} (Δ₁ : TCxt) {P C : Fma}
--                (s : isIrr S) (p : isPos P) 
--                (lf : pos→posat p ⇛lf S ∣ Δ₀) 
--                (f : (∘ , S') MMF.∣ ∘cxt Γ ++ Δ₁ ⇑ (∘ , C)) 
--                (ℓ : MF.L S' Γ P) →
--                S MF.∣ Δ₀ ++ untag-cxt Δ₁ ⇑ C
-- MF-only-lfP' Δ₁ s p lf (⊸r f) ℓ = ⊸r (MF-only-lfP' (Δ₁ ∷ʳ _) s p lf f ℓ)
-- MF-only-lfP' Δ₁ s p lf (Il q f) ℓ = foc s q (focl {Γ₁ = untag-cxt Δ₁} _ (untag-lf lf) (unfoc p (MF.runL ℓ (Il q (untag⇑ {Γ = ∘cxt _ ++ Δ₁} f)))) refl)
-- MF-only-lfP' Δ₁ s p lf (⊗l q f) ℓ = foc s q (focl {Γ₁ = untag-cxt Δ₁} _ (untag-lf lf) (unfoc p (MF.runL ℓ (⊗l q (untag⇑ {Γ = ∘cxt _ ++ Δ₁} f)))) refl)
-- MF-only-lfP' Δ₁ s p lf (foc m q f) ℓ = foc s q (focl {Γ₁ = untag-cxt Δ₁} _ (untag-lf lf) (unfoc p (MF.runL ℓ (foc m q (untag⇓ {Γ = ∘cxt _ ++ Δ₁} f)))) refl)

MF-only-lf-at : {S : Stp} {Δ₀ : Cxt} (Δ₁ : TCxt) {X C : Fma}
                 (s : isIrr S) (x : isAt X) 
                 (lf : at→posat x ⇛lf S ； Δ₀) 
                 (f : (∘ , just X) MMF.∣ Δ₁ ⇑ (∘ , C)) → S MF.∣ Δ₀ ++ untag-cxt Δ₁ ⇑ C
MF-only-lf-at Δ₁ s x lf (⊸r f) = ⊸r (MF-only-lf-at (Δ₁ ∷ʳ _) s x lf f)
MF-only-lf-at Δ₁ s x lf (foc m q (focl {Γ₀ = []} q' blurl f refl refl _)) = foc s q (focl {Γ₁ = untag-cxt Δ₁} _ lf (untag⇓ f) refl)
MF-only-lf-at Δ₁ s x lf (foc m q (focr {Γ₀ = Γ₀}{Γ₁} (just (M , m')) rf (unfoc n f) eq refl _)) = 
  foc s q (focl {Γ₁ = untag-cxt Δ₁} _ lf (focr (just (M , m')) (untag-rf rf) (unfoc (inj₂ (x , n)) (untag⇑ {Γ = ∘tcxt Γ₀} f)) (cong untag-cxt {y = Γ₀ ++ Γ₁} eq)) refl)

MF-only-lf : {S : Stp} {Δ₀ : Cxt} (Δ₁ : TCxt) {Q C : Fma}
             (s : isIrr S) (q : isPosAt Q) 
             (lf : q ⇛lf S ∣ Δ₀) 
             (f : (∘ , just Q) MMF.∣ Δ₁ ⇑ (∘ , C)) → S MF.∣ Δ₀ ++ untag-cxt Δ₁ ⇑ C
MF-only-lf Δ₁ {` X} s q lf f = MF-only-lf-at Δ₁ s q (untag-lf lf) f 
MF-only-lf Δ₁ {I} s q lf f = MF-only-lfP (untag-cxt Δ₁) s q (untag-lf lf) (untag⇑ f) done
MF-only-lf Δ₁ {A ⊗ B} s q lf f = MF-only-lfP (untag-cxt Δ₁) s q (untag-lf lf) (untag⇑ f) done

gen-early-lf : ∀ {S Γ₀ Γ₁} Δ {Q C} {s : isIrr S} {n : isNeg (Δ ⊸⋆ C)} {q : isPos Q}
            {lf : pos→posat q ⇛lf S ； Γ₀} 
            (f : just Q MF.∣ Γ₁ ++ Δ ⇑ C) → 
            unfoc {∘}{∙} {Γ = Γ₀ ++ Γ₁} n (MF.⊸r⋆⇑ Δ (MF-only-lfP (Γ₁ ++ Δ) s q lf f done)) 
              ≗⇓ focl {∙} _ lf (unfoc {∙}{∙} (inj₁ q) (MF.⊸r⋆⇑ Δ f)) refl
gen-early-lf Δ (⊸r f) =
  unfoc-same (refl⇑ (sym (EqC.⊸r⋆⊸r⋆⇑ Δ {_ ∷ []})))
  • gen-early-lf (Δ ∷ʳ _) f
  • focl refl-lf (unfoc-same (refl⇑ (EqC.⊸r⋆⊸r⋆⇑ Δ {_ ∷ []})))
gen-early-lf Δ (Il q f) = early-lf Δ q
gen-early-lf Δ (⊗l q f) = early-lf Δ q
gen-early-lf Δ (foc s q f) = early-lf Δ q

gen-early-lf-at : ∀ {S Γ₀ Γ₁} Δ {X C} {s : isIrr S} {n : isNeg (Δ ⊸⋆ C)} {x : isAt X}
            {lf : at→posat x ⇛lf S ； Γ₀} 
            (f : (∘ , just X) MMF.∣ Γ₁ ++ ∘cxt Δ ⇑ (∘ , C)) → 
            unfoc {∘}{∙} {Γ = Γ₀ ++ untag-cxt Γ₁} n (MF.⊸r⋆⇑ Δ (MF-only-lf-at (Γ₁ ++ ∘cxt Δ) s x lf f)) 
              ≗⇓ focl {∙} _ lf (unfoc {∙}{∙} (inj₂ (x , n)) (MF.⊸r⋆⇑ Δ (untag⇑ f))) refl

gen-early-lf-at Δ (⊸r f) =
  unfoc-same (refl⇑ (sym (EqC.⊸r⋆⊸r⋆⇑ Δ {_ ∷ []})))
  • gen-early-lf-at (Δ ∷ʳ _) f
  • focl refl-lf (unfoc-same (refl⇑ (EqC.⊸r⋆⊸r⋆⇑ Δ {_ ∷ []})))
gen-early-lf-at Δ {x = x} (foc s q (focl {Γ₀ = []} q₁ blurl f refl refl ξ))
  rewrite isProp-isNegAt s (at→negat x) | isProp-isPosAt q₁ (at→posat x) = early-lf-at Δ q
gen-early-lf-at {Γ₁ = Γ₁} Δ {x = x} (foc s q (focr {Γ₀ = Γ₂} {Γ₃} (just (M , m)) rf (unfoc ok f) eq refl ξ)) with ++? Γ₂ Γ₁ Γ₃ (∘cxt Δ) eq
gen-early-lf-at {Γ₁ = .(Γ₂ ++ A ∷ Ω)} Δ {X = ` X} {x = x} (foc s q (focr {Γ₀ = Γ₂} {.(A ∷ Ω ++ map (λ A₁ → ∘ , A₁) Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ)) | inj₂ (A , Ω , refl , refl) =
  early-lf-at {Γ₁ = _ ++ _ ∷ _} Δ q {eq = refl}
  • focl refl-lf (unfoc-same (cong⊸r⋆⇑ Δ (foc-same (swap • focr refl-rf blurl-at))))
... | inj₁ (Ω , r , refl) with split-map ∘fma Δ Ω Γ₃ r
gen-early-lf-at {Γ₁ = Γ₁} Δ {X = ` X} {x = x} (foc s q (focr {_} {_} {_} {_} {_} {.(Γ₁ ++ map (λ A → ∘ , A) Ω')} {.(map (λ A → ∘ , A) Γ₃')} (just (M , m)) rf (unfoc ok f) refl refl ξ)) | inj₁ (.(map (λ A → ∘ , A) Ω') , r , refl) | Ω' , Γ₃' , refl , refl , refl =
  early-lf-at Δ q {eq = refl}
  • focl refl-lf (unfoc-same (cong⊸r⋆⇑ Δ (foc-same (swap • focr refl-rf blurl-at))))


untag-only-lf⇑ : {S : Stp} {Δ₀ : Cxt} (Δ₁ : TCxt) {Q C : Fma}
               (s : isIrr S) (q : isPosAt Q)
               (lf : q ⇛lf S ∣ Δ₀) 
               (f : (∘ , just Q) MMF.∣ Δ₁ ⇑ (∘ , C)) →
               untag⇑ (only-lf⇑ Δ₁ s q lf f) ≗⇑ MF-only-lf Δ₁ s q lf f

untag-only-lfP : {S S' : Stp} {Δ₀ : Cxt} (Δ₁ : TCxt) {Γ : Cxt} {P C : Fma}
            (s : isIrr S) (p : isPos P)
            (lf : pos→posat p ⇛lf S ∣ Δ₀) 
            (f : (∘ , S') MMF.∣ ∘cxt Γ ++ Δ₁ ⇑ (∘ , C)) → 
            (ℓ : MF.L S' Γ P) → 
            untag⇑ (only-lf⇑P Δ₁ s p lf f ℓ) ≗⇑ MF-only-lfP (untag-cxt Δ₁) s p (untag-lf lf) (untag⇑ f) ℓ

untag-only-lf-fP : {S S' : Stp} {Δ : TCxt} {Δ₀ : Cxt} (Δ₁ : TCxt) {Γ : Cxt} {Q P : Fma}
            (s' : isIrr S') (p : isPos P) (q : isPosAt Q)
            (lf : pos→posat p ⇛lf S ∣ Δ₀) 
            (f : MMF.[ ∘ , ∘ ] (∘ , S') ∣ Δ ⇓ (∘ , Q)) → 
            (eq : Δ ≡ ∘cxt Γ ++ Δ₁)
            (ℓ : MF.L S' Γ P) →
            untag⇓ (only-lf-fP Δ₁ s' p q lf f eq ℓ) ≗⇓
              focl {Γ₁ = untag-cxt Δ₁} _ (untag-lf lf) (unfoc p (MF.runL ℓ (foc s' q (untag⇓ {Γ = ∘cxt Γ ++ Δ₁} (subst⇓ f eq))))) refl

untag-only-lf-at : {S : Stp} {Δ₀ : Cxt} (Δ₁ : TCxt) {X C : Fma}
               (s : isIrr S) (x : isAt X)
               (lf : at→posat x ⇛lf S ∣ Δ₀) 
               (f : (∘ , just X) MMF.∣ Δ₁ ⇑ (∘ , C)) →
               untag⇑ (only-lf⇑-at Δ₁ s x lf f) ≗⇑ MF-only-lf-at Δ₁ s x (untag-lf lf) f

untag-only-lf-at = {!!}

untag-only-lf⇑ Δ₁ {` X} = untag-only-lf-at Δ₁
untag-only-lf⇑ Δ₁ {I} s q lf f = untag-only-lfP Δ₁ s tt lf f done
untag-only-lf⇑ Δ₁ {A ⊗ B} s q lf f = untag-only-lfP Δ₁ s tt lf f done

untag-only-lfP Δ₁ s p lf (⊸r f) ℓ = ⊸r (untag-only-lfP (Δ₁ ∷ʳ _) s p lf f ℓ)
untag-only-lfP Δ₁ s p lf (Il q f) ℓ = 
  trans⇑ (untag-only-lfP Δ₁ s p lf f (MF.Il-1 ℓ))
         (trans⇑ (refl⇑ (MF-only-lfP-eq (untag-cxt Δ₁) s p q (untag-lf lf) (untag⇑ f) (Il-1 ℓ)))
                 (foc-same (focl refl-lf {eq = refl} (unfoc-same (refl⇑ (cong (MF.runL ℓ) (EqC.Il⇑eq _)))))))
untag-only-lfP Δ₁ s p lf (⊗l q f) ℓ = 
  trans⇑ (untag-only-lfP Δ₁ s p lf f (MF.⊗l-1 ℓ))
         (trans⇑ (refl⇑ (MF-only-lfP-eq (untag-cxt Δ₁) s p q (untag-lf lf) (untag⇑ f) (⊗l-1 ℓ)))
                 (foc-same (focl refl-lf {eq = refl} (unfoc-same (refl⇑ (cong (MF.runL ℓ) (EqC.⊗l⇑eq _)))))))

untag-only-lfP Δ₁ s p lf (foc s₁ q f) ℓ = foc-same (untag-only-lf-fP Δ₁ s₁ p q lf f refl ℓ)

{-
untag-only-lf⇑P : {S S' : Stp} {Δ₀ : Cxt} (Δ₁ : TCxt) {Γ : Cxt} {P Q : Fma}
            (s : isIrr S) (p : isPos P) (q : isPosAt Q)
            (lf : pos→posat p ⇛lf S ∣ Δ₀) 
            (f : (∘ , S') MMF.∣ ∘cxt Γ ++ Δ₁ ⇑ (∘ , Q)) → 
            (ℓ : MF.L S' Γ P) →
            untag⇑ (only-lf⇑P Δ₁ s p lf f ℓ) ≗⇑ 
              foc s q (focl {Γ₁ = untag-cxt Δ₁} _ (untag-lf lf) (unfoc p (MF.runL ℓ (untag⇑ {Γ = ∘cxt Γ ++ Δ₁} f))) refl)

untag-only-lf-fP : {S S' : Stp} {Δ : TCxt} {Δ₀ : Cxt} (Δ₁ : TCxt) {Γ : Cxt} {Q P : Fma}
            (s' : isIrr S') (p : isPos P) (q : isPosAt Q)
            (lf : pos→posat p ⇛lf S ∣ Δ₀) 
            (f : MMF.[ ∘ , ∘ ] (∘ , S') ∣ Δ ⇓ (∘ , Q)) → 
            (eq : Δ ≡ ∘cxt Γ ++ Δ₁)
            (ℓ : MF.L S' Γ P) →
            untag⇓ (only-lf-fP Δ₁ s' p q lf f eq ℓ) ≗⇓
              focl {Γ₁ = untag-cxt Δ₁} _ (untag-lf lf) (unfoc p (MF.runL ℓ (foc s' q (untag⇓ {Γ = ∘cxt Γ ++ Δ₁} (subst⇓ f eq))))) refl


untag-only-lf⇑P Δ₁ s p q lf (Il q₁ f) ℓ =
  trans⇑ (untag-only-lf⇑P Δ₁ s p q lf f (MF.Il-1 ℓ))
         (foc-same (focl refl-lf (unfoc-same (refl⇑ (cong (MF.runL ℓ) (EqC.Il⇑eq _))))))
untag-only-lf⇑P Δ₁ s p q lf (⊗l q₁ f) ℓ =
  trans⇑ (untag-only-lf⇑P Δ₁ s p q lf f (MF.⊗l-1 ℓ))
         (foc-same (focl refl-lf (unfoc-same (refl⇑ (cong (MF.runL ℓ) (EqC.⊗l⇑eq _))))))
untag-only-lf⇑P Δ₁ s p q lf (foc s₁ q₁ f) ℓ rewrite isProp-isPosAt q q₁ =
  foc-same (untag-only-lf-fP Δ₁ s₁ p q₁ lf f refl ℓ)
-}

untag-only-lf-fP Δ₁ {Γ} s' p q lf (focl {Γ₀ = Γ₀} {Γ₁} q₁ lf₁ (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) refl refl ξ) eq ℓ with  ++?-alt (∘cxt Γ) Γ₀ Δ₁ Γ₁ eq
untag-only-lf-fP .(Ω ++ Γ₁) {Γ} s' p q lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ ++ Ω)} {Γ₁} q₁ lf₁ (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (Ω , refl , refl) =
  focl refl-lf
       (focr refl-rf {eq' = refl} (unfoc-same (refl⇑ (trans (cong (untag⇑ {Γ = ∘tcxt Ω}) (sym (Lem.runLeq ℓ))) (untag-runL {Δ = ∘tcxt Ω} ℓ _))))
       • focr refl-rf (unfoc-same (congrunL ℓ (foc-same swap)))
       • (~ early-rf-at s' ℓ)
       • unfoc-same (congrunL ℓ (foc-same (~ swap))))
... | inj₂ (A , Ω , eq' , refl) with split-map ∘fma Γ Γ₀ (A ∷ Ω) eq'
untag-only-lf-fP Δ₁ {.(Γ₀' ++ _ ∷ Ω')} s' p q lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₀')} {.((∘ , _) ∷ map (λ A → ∘ , A) Ω' ++ Δ₁)} q₁ lf₁ (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) refl refl ξ) refl ℓ | inj₂ (.(∘ , _) , .(map (λ A → ∘ , A) Ω') , eq' , refl) | Γ₀' , _ ∷ Ω' , refl , refl , refl =
  focl refl-lf
       (unfoc-same (refl⇑ (trans (cong (untag⇑ {Γ = ∘tcxt Δ₁}) (sym (Lem.runLeq ℓ))) (untag-runL {Δ = ∘tcxt Δ₁} ℓ _))))
untag-only-lf-fP Δ₁ {Γ} s' p q lf (focl {Γ₀ = Γ₂} q₁ lf₁ (focr {Γ₀ = Γ₀} {Γ₁} (just x) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ  with ++?-alt (∘cxt Γ) (Γ₂ ++ Γ₀) Δ₁ Γ₁ eq
... | inj₁ (Ω , eq' , refl) with ++?-alt (∘cxt Γ) Γ₂ Ω Γ₀ eq'
untag-only-lf-fP .((Λ ++ Γ₀) ++ Γ₁) {Γ} s' p q lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ ++ Λ)} q₁ lf₁ (focr {Γ₀ = Γ₀} {Γ₁} (just (A ⊸ B , n)) rf (unfoc (inj₁ p') f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(Λ ++ Γ₀) , eq' , refl) | inj₁ (Λ , refl , refl) rewrite isProp-isPosAt q₁ (pos→posat p') =
  focl refl-lf
       (focr refl-rf {eq' = refl} (unfoc-same (refl⇑ (untag-runL {Δ = ∘tcxt (Λ ++ Γ₀)} ℓ _)))
       • focr refl-rf {eq' = refl} (unfoc-same (congrunL ℓ (refl⇑ (cong (untag⇑ {Γ = ∘cxt Γ ++ ∘tcxt (Λ ++ Γ₀)}) (only-lf⇑≡ {Δ₀ = Γ ++ untag-cxt Λ} f)))))
       • focr refl-rf {eq' = refl} (unfoc-same (congrunL ℓ (untag-only-lfP (∘tcxt Γ₀) s' p' lf₁ f done)))
       • (~ early-rf s' {r = q} ℓ)
       • unfoc-same (congrunL ℓ (foc-same (focr refl-rf (gen-early-lf [] _) • ~ swap))))
untag-only-lf-fP .((Λ ++ Γ₀) ++ Γ₁) {Γ} s' p q lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ ++ Λ)} q₁ lf₁ (focr {Γ₀ = Γ₀} {Γ₁} (just (` X , x)) rf (unfoc (inj₁ p') f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(Λ ++ Γ₀) , eq' , refl) | inj₁ (Λ , refl , refl) rewrite isProp-isPosAt q₁ (pos→posat p') =
  focl refl-lf
       (focr refl-rf {eq' = refl} (unfoc-same (refl⇑ (untag-runL {Δ = ∘tcxt (Λ ++ Γ₀)} ℓ _)))
       • focr refl-rf {eq' = refl} (unfoc-same (congrunL ℓ
           (trans⇑ (refl⇑ (cong (untag⇑ {Γ = ∘cxt Γ ++ ∘tcxt (Λ ++ Γ₀)}) (only-lf⇑≡ {Δ₀ = Γ ++ untag-cxt Λ} f)))
                   (trans⇑ (untag-only-lfP (∘tcxt Γ₀) s' p' lf₁ f done)
                           (trans⇑ (refl⇑ (MF-only-lfP-eq (untag-cxt Γ₀) s' p' tt (untag-lf lf₁) (untag⇑ f) done))
                                   (foc-same (focl refl-lf (~ blurr-at) • swap)))))))
       • (~ early-rf-at s' ℓ)
       • unfoc-same (congrunL ℓ (foc-same (~ swap))))
untag-only-lf-fP .((Λ ++ Γ₀) ++ Γ₁) {Γ} s' p q lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ ++ Λ)} {Q = ` X} q₁ lf₁ (focr {Γ₀ = Γ₀} {Γ₁} (just (A ⊸ B , _)) rf (unfoc (inj₂ (x' , n)) f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(Λ ++ Γ₀) , eq' , refl) | inj₁ (Λ , refl , refl) =
  focl refl-lf
       (focr refl-rf {eq' = refl} (unfoc-same (refl⇑ (untag-runL {Δ = ∘tcxt (Λ ++ Γ₀)} ℓ _)))
       • focr refl-rf {eq' = refl} (unfoc-same (congrunL ℓ (untag-only-lf-at (∘tcxt Γ₀) s' q₁ lf₁ f)))
       • (~ early-rf s' {r = q} ℓ)
       • unfoc-same (congrunL ℓ (foc-same (focr refl-rf (gen-early-lf-at [] {lf = untag-lf lf₁} f) • ~ swap))))
... | inj₂ (A' , Λ , eq'' , refl) with split-map ∘fma Γ Γ₂ (_ ∷ Λ) eq''
untag-only-lf-fP .(Ω ++ Γ₁) {.(Γ₂' ++ _ ∷ Λ')} s' p q lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₂')} q₁ lf₁ (focr {_} {_} {_} {_} {_} {.((∘ , _) ∷ map (λ A → ∘ , A) Λ' ++ Ω)} {Γ₁} (just (A ⊸ B , n)) rf (unfoc (inj₁ p') f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (Ω , eq' , refl) | inj₂ (.(∘ , _) , .(map (λ A → ∘ , A) Λ') , eq'' , refl) | Γ₂' , _ ∷ Λ' , refl , refl , refl
  rewrite isProp-isPosAt q₁ (pos→posat p') =
  focl refl-lf
       (focr refl-rf {eq' = refl} (unfoc-same (refl⇑ (untag-runL {Δ = ∘tcxt Ω} ℓ _)))
       • focr refl-rf {eq' = refl} (unfoc-same (congrunL ℓ
            (trans⇑ (refl⇑ (cong (untag⇑ {Γ = ∘cxt (Γ₂' ++ _ ∷ Λ') ++ ∘tcxt Ω}) (only-lf⇑≡ {Δ₀ = Γ₂'} f)))
                    (untag-only-lfP (_ ∷ ∘cxt Λ' ++ ∘tcxt Ω) s' p' lf₁ f done))))
       • ~ early-rf s' {r = q} ℓ {eq = refl}
       • unfoc-same (congrunL ℓ (foc-same (focr refl-rf (gen-early-lf [] _) • ~ swap))))
untag-only-lf-fP .(Ω ++ Γ₁) {.(Γ₂' ++ _ ∷ Λ')} s' p q lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₂')} q₁ lf₁ (focr {_} {_} {_} {_} {_} {.((∘ , _) ∷ map (λ A → ∘ , A) Λ' ++ Ω)} {Γ₁} (just (` X , x)) rf (unfoc (inj₁ p') f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (Ω , eq' , refl) | inj₂ (.(∘ , _) , .(map (λ A → ∘ , A) Λ') , eq'' , refl) | Γ₂' , _ ∷ Λ' , refl , refl , refl
  rewrite isProp-isPosAt q₁ (pos→posat p') =
  focl refl-lf
       (focr refl-rf {eq' = refl} (unfoc-same (refl⇑ (untag-runL {Δ = ∘tcxt Ω} ℓ _)))
       • focr refl-rf {eq' = refl} (unfoc-same (congrunL ℓ
            (trans⇑ (refl⇑ (cong (untag⇑ {Γ = ∘cxt (Γ₂' ++ _ ∷ Λ') ++ ∘tcxt Ω}) (only-lf⇑≡ {Δ₀ = Γ₂'} f)))
                    (trans⇑ (untag-only-lfP (_ ∷ ∘cxt Λ' ++ ∘tcxt Ω) s' p' lf₁ f done)
                            (trans⇑ (refl⇑ (MF-only-lfP-eq _ s' p' tt (untag-lf lf₁) (untag⇑ f) done))
                                   (foc-same (focl refl-lf (~ blurr-at) • swap)))))))
       • (~ early-rf-at s' ℓ)
       • unfoc-same (congrunL ℓ (foc-same (~ swap))))
untag-only-lf-fP .(Ω ++ Γ₁) {.(Γ₂' ++ _ ∷ Λ')} s' p q lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₂')} {Q = ` X} q₁ lf₁ (focr {_} {_} {_} {_} {_} {.((∘ , _) ∷ map (λ A → ∘ , A) Λ' ++ Ω)} {Γ₁} (just (_ ⊸ _ , _)) rf (unfoc (inj₂ (x , m)) f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (Ω , eq' , refl) | inj₂ (.(∘ , _) , .(map (λ A → ∘ , A) Λ') , eq'' , refl) | Γ₂' , _ ∷ Λ' , refl , refl , refl = 
  focl refl-lf
       (focr refl-rf {eq' = refl} (unfoc-same (refl⇑ (untag-runL {Δ = ∘tcxt Ω} ℓ _)))
       • focr refl-rf {eq' = refl} (unfoc-same (congrunL ℓ (untag-only-lf-at (∘fma _ ∷ ∘cxt Λ' ++ ∘tcxt Ω)  s' _ lf₁ f)))
       • (~ early-rf s' {r = q} ℓ)
       • unfoc-same (congrunL ℓ (foc-same (focr refl-rf (gen-early-lf-at [] {lf = untag-lf lf₁} f) • ~ swap))))
untag-only-lf-fP Δ₁ {Γ} s' p q lf (focl {Γ₀ = Γ₂} q₁ lf₁ (focr {Γ₀ = Γ₀} {.(A ∷ Ω ++ Δ₁)} (just x) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ | inj₂ (A , Ω , eq' , refl) with split-map ∘fma Γ Γ₂ (Γ₀ ++ _ ∷ Ω) eq'
... | (Γ₂' , Λ , refl , eq'' , refl) with split-map ∘fma Λ Γ₀ (_ ∷ Ω) eq''
untag-only-lf-fP Δ₁ {.(Γ₂' ++ Γ₀' ++ _ ∷ Ω')} s' p q lf (focl {_} {_} {_} {_} {.(map _ Γ₂')} q₁ lf₁ (focr {Γ₀ = .(map (λ A → ∘ , A) Γ₀')} {.((∘ , _) ∷ map (λ A → ∘ , A) Ω' ++ Δ₁)} (just x) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₂ (.(∘ , _) , .(map (λ A → ∘ , A) Ω') , eq' , refl) | Γ₂' , .(Γ₀' ++ _ ∷ Ω') , refl , eq'' , refl | Γ₀' , _ ∷ Ω' , refl , refl , refl =
  focl refl-lf
       (unfoc-same (refl⇑ (trans (cong (untag⇑ {Γ = ∘tcxt Δ₁}) (sym (Lem.runLeq ℓ))) (untag-runL {Δ = ∘tcxt Δ₁} ℓ _))))
untag-only-lf-fP Δ₁ {Γ} s' p q lf (focl {Γ₀ = Γ₀} {Γ₁} q₁ lf₁ (unfoc ok f) refl refl ξ) eq ℓ with ++?-alt (∘cxt Γ) Γ₀ Δ₁ Γ₁ eq
untag-only-lf-fP .(Ω ++ Γ₁) {Γ} s' p q lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ ++ Ω)} {Γ₁} q₁ lf₁ (unfoc ok f) refl refl ξ) refl ℓ | inj₁ (Ω , refl , refl) =
  focl refl-lf (unfoc-same (refl⇑ (trans (cong (untag⇑ {Γ = ∘tcxt (Ω ++ Γ₁)}) (sym (Lem.runLeq ℓ))) (untag-runL {Δ = ∘tcxt (Ω ++ Γ₁)} ℓ _))))
... | inj₂ (A , Ω , eq' , refl)  with split-map ∘fma Γ Γ₀ (A ∷ Ω) eq'
untag-only-lf-fP Δ₁ {.(Γ₀' ++ _ ∷ Ω')} s' p q lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₀')} {.((∘ , _) ∷ map (λ A → ∘ , A) Ω' ++ Δ₁)} q₁ lf₁ (unfoc ok f) refl refl ξ) refl ℓ | inj₂ (.(∘ , _) , .(map (λ A → ∘ , A) Ω') , eq' , refl) | Γ₀' , _ ∷ Ω' , refl , refl , refl =
  focl refl-lf
       (unfoc-same (refl⇑ (trans (cong (untag⇑ {Γ = ∘tcxt Δ₁}) (sym (Lem.runLeq ℓ))) (untag-runL {Δ = ∘tcxt Δ₁} ℓ _))))
untag-only-lf-fP Δ₁ {Γ} s' p q lf (focr {Γ₀ = Γ₀} {Γ₁} (just x) rf (unfoc ok f) refl refl ξ) eq ℓ with ++?-alt (∘cxt Γ) Γ₀ Δ₁ Γ₁ eq
untag-only-lf-fP .(Ω ++ Γ₁) {Γ} s' p q lf (focr {Γ₀ = .(map (λ A → ∘ , A) Γ ++ Ω)} {Γ₁} (just (_ ⊸ _ , _)) rf (unfoc ok f) refl refl ξ) refl ℓ | inj₁ (Ω , refl , refl) =
  focl refl-lf
       (focr refl-rf {eq' = refl} (unfoc-same (refl⇑ (untag-runL {Δ = ∘tcxt Ω} ℓ _))) 
       • ~ early-rf s' {r = q} ℓ
       • unfoc-same (congrunL ℓ (foc-same (focr refl-rf (unfoc-same (refl⇑ (untag-l∙→∘⇑ f)))))))
... | inj₂ (A , Ω , eq' , refl) with split-map ∘fma Γ Γ₀ (A ∷ Ω) eq'
untag-only-lf-fP Δ₁ {.(Γ₀' ++ _ ∷ Ω')} s' p q lf (focr {Γ₀ = .(map (λ A → ∘ , A) Γ₀')} {.((∘ , _) ∷ map (λ A → ∘ , A) Ω' ++ Δ₁)} (just x) rf (unfoc ok f) refl refl ξ) refl ℓ | inj₂ (.(∘ , _) , .(map (λ A → ∘ , A) Ω') , eq' , refl) | Γ₀' , _ ∷ Ω' , refl , refl , refl =
  focl refl-lf
       (unfoc-same (refl⇑ (trans (cong (untag⇑ {Γ = ∘tcxt Δ₁}) (sym (Lem.runLeq ℓ))) (untag-runL {Δ = ∘tcxt Δ₁} ℓ _))))
untag-only-lf-fP Δ₁ s' p q lf (focr ─ rf (refl , refl) refl refl ξ) refl ℓ =
  focl refl-lf
       (unfoc-same (refl⇑ (trans (cong (untag⇑ {Γ = ∘tcxt Δ₁}) (sym (Lem.runLeq ℓ))) (untag-runL {Δ = ∘tcxt Δ₁} ℓ _))))

untag⇑∘max : ∀ {S Γ A} (f : S MF.∣ Γ ⇑ A) → untag⇑ (max f) ≗⇑ f
untag∘max-lf : ∀ {S Γ Q} {q : isPosAt Q} (f : q MF.⇛lf S ； Γ)
  → untag-lf (max-lf f) ≗lf f
untag∘max-rf : ∀ {Γ A} {s : Maybe (Σ Fma isNegAt)} (f : s MF.⇛rf Γ ； A)
  → untag-rf (max-rf f) ≗rf f
untag∘maxs : ∀ {Ξ} (fs : All (λ ΔB → ─ MF.∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ)
  → untags⇑ (maxs fs) ≗s⇑ fs

untag∘max-lf (pass f) = pass (untag∘max-lf f)
untag∘max-lf (⊸l+ Γ₀ Ξ q fs f refl) = ⊸l+ (untag∘maxs fs) (untag∘max-lf f)
untag∘max-lf blurl = blurl

untag∘max-rf Ir = Ir
untag∘max-rf (⊗r+ Δ₀ Ξ m f gs refl) = ⊗r+ (untag∘max-rf f) (untag∘maxs gs)
untag∘max-rf blurr = blurr

untag∘maxs [] = []
untag∘maxs (f ∷ fs) = (untag⇑∘max f) ∷ (untag∘maxs fs)

untag⇑∘max (⊸r f) = ⊸r (untag⇑∘max f)
untag⇑∘max (Il q f) = Il (untag⇑∘max f)
untag⇑∘max (⊗l q f) = ⊗l (untag⇑∘max f)
untag⇑∘max (foc s q (focl q₁ lf (focr (just (.(` _) , snd)) rf ax refl) refl)) = foc (focl (untag∘max-lf lf) (focr (untag∘max-rf rf) refl))
untag⇑∘max (foc s q (focl q₁ lf (focr (just x) rf (unfoc ok f) refl) refl)) = foc (focl (untag∘max-lf lf) (focr (untag∘max-rf rf) (unfoc (untag⇑∘max f))))
untag⇑∘max (foc s q (focl {Γ₀ = Γ₀}{Γ₁} q₁ lf (unfoc ok f) refl))
  rewrite isProp-isPosAt q₁ (pos→posat ok) =
  trans⇑ (refl⇑ (cong (untag⇑ {Γ = ∘cxt Γ₀ ++ ∘cxt Γ₁}) (only-lf⇑≡ (max f))))
         (trans⇑ (untag-only-lfP (∘cxt Γ₁) s ok (max-lf lf) (max f) done)
                 (trans⇑ {!!}
                         (refl⇑ (MF-only-lfP-eq Γ₁ s ok q lf f done))))
untag⇑∘max (foc s q (focr (just (.(` _) , snd)) rf (focl q₁ lf ax refl) refl)) = foc (swap • focr (untag∘max-rf rf) (focl (untag∘max-lf lf) refl))
untag⇑∘max (foc s q (focr (just x) rf (focl q₁ lf (unfoc ok f) refl) refl)) = foc (swap • focr (untag∘max-rf rf) (focl (untag∘max-lf lf) (unfoc (untag⇑∘max f))))
untag⇑∘max (foc s q (focr (just x) rf (unfoc ok f) refl)) = {!!}
untag⇑∘max (foc s q (focr ─ rf (refl , refl) refl)) = foc (focrn (untag∘max-rf rf))

