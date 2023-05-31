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

untag-only-lf⇑ : {S : Stp} {Δ₀ : Cxt} (Δ₁ : TCxt) {Q Q' : Fma}
               (s : isIrr S) (q : isPosAt Q) (q' : isPosAt Q')
               (lf : q ⇛lf S ∣ Δ₀) 
               (f : (∘ , just Q) MMF.∣ Δ₁ ⇑ (∘ , Q')) →
               untag⇑ (only-lf⇑ Δ₁ s q lf f) ≡
                 foc s q' (focl {Γ₁ = untag-cxt Δ₁} _ (untag-lf lf) (unfoc {!!} {!!}) {!!})

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
untag-only-lf-fP .((Λ ++ Γ₀) ++ Γ₁) {Γ} s' p q lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ ++ Λ)} q₁ lf₁ (focr {Γ₀ = Γ₀} {Γ₁} (just (Q' , q')) rf (unfoc (inj₁ p') f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(Λ ++ Γ₀) , eq' , refl) | inj₁ (Λ , refl , refl) rewrite isProp-isPosAt q₁ (pos→posat p') =
  focl refl-lf
       (focr refl-rf {eq' = refl} (unfoc-same (refl⇑ (untag-runL {Δ = ∘tcxt (Λ ++ Γ₀)} ℓ _)))
       • focr refl-rf {eq' = refl} (unfoc-same (congrunL ℓ (refl⇑ (cong (untag⇑ {Γ = ∘cxt Γ ++ ∘tcxt (Λ ++ Γ₀)}) (only-lf⇑≡ {Δ₀ = Γ ++ untag-cxt Λ} f)))))
       • focr refl-rf {eq' = refl} (unfoc-same (congrunL ℓ {!untag-only-lf⇑P doesn't work!}))
       • {!!}
       • unfoc-same (congrunL ℓ (foc-same (~ swap))))
--       (focr refl-rf {eq' = refl} (unfoc-same (refl⇑ (trans (cong (untag⇑ {Γ = ∘tcxt Ω}) (sym (Lem.runLeq ℓ))) (untag-runL {Δ = ∘tcxt Ω} ℓ _))))
--       • focr refl-rf (unfoc-same (congrunL ℓ (foc-same swap)))
--       • (~ early-rf-at s' ℓ)
untag-only-lf-fP .((Λ ++ Γ₀) ++ Γ₁) {Γ} s' p q lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ ++ Λ)} q₁ lf₁ (focr {Γ₀ = Γ₀} {Γ₁} (just x) rf (unfoc (inj₂ (x' , n)) f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(Λ ++ Γ₀) , eq' , refl) | inj₁ (Λ , refl , refl) =
  focl refl-lf
       (focr refl-rf {eq' = refl} (unfoc-same (refl⇑ (untag-runL {Δ = ∘tcxt (Λ ++ Γ₀)} ℓ _)))
       • focr refl-rf (unfoc-same (congrunL ℓ {!!}))
       • (~ {!!})
       • unfoc-same (congrunL ℓ (foc-same (~ swap))))
--       (focr refl-rf {eq' = refl} (unfoc-same (refl⇑ (trans (cong (untag⇑ {Γ = ∘tcxt Ω}) (sym (Lem.runLeq ℓ))) (untag-runL {Δ = ∘tcxt Ω} ℓ _))))
--       • focr refl-rf (unfoc-same (congrunL ℓ (foc-same swap)))
--       • (~ early-rf-at s' ℓ)
       
... | inj₂ (A' , Λ , eq'' , refl) with split-map ∘fma Γ Γ₂ (_ ∷ Λ) eq''
untag-only-lf-fP .(Ω ++ Γ₁) {.(Γ₂' ++ _ ∷ Λ')} s' p q lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₂')} q₁ lf₁ (focr {_} {_} {_} {_} {_} {.((∘ , _) ∷ map (λ A → ∘ , A) Λ' ++ Ω)} {Γ₁} (just x) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (Ω , eq' , refl) | inj₂ (.(∘ , _) , .(map (λ A → ∘ , A) Λ') , eq'' , refl) | Γ₂' , _ ∷ Λ' , refl , refl , refl =
  focl refl-lf
       {!same as above!}
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
untag-only-lf-fP .(Ω ++ Γ₁) {Γ} s' p q lf (focr {Γ₀ = .(map (λ A → ∘ , A) Γ ++ Ω)} {Γ₁} (just x) rf (unfoc ok f) refl refl ξ) refl ℓ | inj₁ (Ω , refl , refl) =
  focl refl-lf {!!}
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
untag⇑∘max (foc s q (focl q₁ lf (unfoc ok f) refl)) = {!!}
untag⇑∘max (foc s q (focr (just (.(` _) , snd)) rf (focl q₁ lf ax refl) refl)) = foc (swap • focr (untag∘max-rf rf) (focl (untag∘max-lf lf) refl))
untag⇑∘max (foc s q (focr (just x) rf (focl q₁ lf (unfoc ok f) refl) refl)) = foc (swap • focr (untag∘max-rf rf) (focl (untag∘max-lf lf) (unfoc (untag⇑∘max f))))
untag⇑∘max (foc s q (focr (just x) rf (unfoc ok f) refl)) = {!!}
untag⇑∘max (foc s q (focr ─ rf (refl , refl) refl)) = foc (focrn (untag∘max-rf rf))
