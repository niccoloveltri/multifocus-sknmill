{-# OPTIONS --rewriting #-}

module correct.max-multifocus.Iso1 where

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
open import correct.max-multifocus.Lemmata

max∘untag⇑ : ∀ {S Γ A} (f : (∘ , S) MMF.∣ Γ ⇑ (∘ , A)) → max (untag⇑ f) ≡ untag-seq f
max∘untag⇓ : ∀ {S Γ A s q} (f : MMF.[ ∘ , ∘ ] (∘ , S) ∣ Γ ⇓ (∘ , A))
  → max (foc s q (untag⇓ f)) ≡ foc s q (untag-seq-f f)

max∘untag⇑r∙ : ∀ {S Γ A} (f : (∘ , S) MMF.∣ Γ ⇑ (∙ , A))
  → max (untag⇑ f) ≡ r∙→∘⇑ f
max∘untag⇓r∙ : ∀ {S Γ A s q} (f : MMF.[ ∘ , ∘ ] (∘ , S) ∣ Γ ⇓ (∙ , A))
  → max (foc s q (untag⇓ f)) ≡ r∙→∘⇑ (foc s q f)

max∘untag⇑l∙ : ∀ {S Γ A} (f : (∙ , S) MMF.∣ Γ ⇑ (∘ , A))
  → max (untag⇑ f) ≡ l∙→∘⇑ f
max∘untag⇓l∙ : ∀ {S Γ A s q} (f : MMF.[ ∘ , ∘ ] (∙ , S) ∣ Γ ⇓ (∘ , A))
  → max (foc s q (untag⇓ f)) ≡ l∙→∘⇑ (foc s q f)

max∘untag-lf : ∀ {S Γ Q} {q : isPosAt Q} (lf : q ⇛lf S ∣ Γ)
  → max-lf (untag-lf lf) ≡ lf
max∘untag-rf : ∀ {Γ A} {s : Maybe (Σ Fma isNegAt)} (rf : s MMF.⇛rf Γ ； A)
  → max-rf (untag-rf rf) ≡ rf
max∘untags⇑ : ∀ {Ξ} (fs : All (λ ΔB → (∘ , ─) MMF.∣ ∘cxt (proj₁ ΔB) ⇑ ∘fma (proj₂ ΔB)) Ξ)
  → maxs (untags⇑ fs) ≡ fs


max∘untags⇑ [] = refl
max∘untags⇑ (_∷_ {Γ , _} f fs) =
  cong₂ _∷_ (trans (max∘untag⇑ f) (untag-seq≡ {Γ = ∘cxt Γ} {∘cxt Γ} f refl)) (max∘untags⇑ fs)

max∘untag-lf (pass lf) = cong pass (max∘untag-lf lf)
max∘untag-lf (⊸l+ Γ₀ Ξ q fs lf) = cong₂ (⊸l+ Γ₀ Ξ q) (max∘untags⇑ fs) (max∘untag-lf lf)
max∘untag-lf blurl = refl

max∘untag-rf Ir = refl
max∘untag-rf (⊗r+ Δ₀ Ξ m rf gs) = cong₂ (⊗r+ Δ₀ Ξ m) (max∘untag-rf rf) (max∘untags⇑ gs)
max∘untag-rf blurr = refl

max∘untag⇑ {Γ = Γ} (⊸r f) = cong ⊸r (max∘untag⇑ {Γ = Γ ∷ʳ _} f)
max∘untag⇑ (Il q f) = cong (Il q) (max∘untag⇑ f)
max∘untag⇑ (⊗l q f) = cong (⊗l q) (max∘untag⇑ f)
max∘untag⇑ (foc s q f) = max∘untag⇓ f

max∘untag⇓ (focl {Γ₀ = Γ₀} {Γ₁} q lf (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) refl refl ξ) = congfoc (congfocl (max∘untag-lf lf) (congfocr (max∘untag-rf rf) refl))
max∘untag⇓ (focl {Γ₀ = Γ₂} q lf (focr {Γ₀ = Γ₀} {Γ₁} (just x) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) =
  congfoc (congfocl (max∘untag-lf lf) (congfocr (max∘untag-rf rf) (cong (unfoc {Γ = ∘tcxt Γ₀} ok) (trans (max∘untag⇑ f) (untag-seq≡ {Γ = ∘tcxt Γ₀} {∘tcxt Γ₀} f refl)))))
max∘untag⇓ {s = s} (focl {Γ₀ = Γ₀} {Γ₁} q lf (unfoc ok f) refl refl ξ)
  rewrite isProp-isPosAt q (pos→posat ok) =
  trans (cong-only-lf⇑ (max∘untag-lf lf) (max∘untag⇑r∙ f))
        (trans (only-lf⇑≡ {Δ₁ = ∘tcxt Γ₁} {lf = lf} _)
               (only-lf⇑P-r∙ {Δ₁ = untag-cxt Γ₁}{[]} {lf = lf} f _))
max∘untag⇓ {Γ = .(Γ₀ ++ Γ₁)} (focr {Γ₀ = Γ₀} {Γ₁} (just (_ ⊸ _ , _)) rf (unfoc ok f) refl refl ξ) =
  trans (cong-only-rf⇑ (max∘untag-rf rf) (max∘untag⇑l∙ f))
        (only-rf⇑N-l∙ {Δ₀ = untag-cxt Γ₀} {_}{[]} f)
max∘untag⇓ (focr ─ rf (refl , refl) refl refl ξ) = congfoc (congfocr (max∘untag-rf rf) refl)

max∘untag⇑r∙ (Il q f) = cong (Il q) (max∘untag⇑r∙ f)
max∘untag⇑r∙ (⊗l q f) = cong (⊗l q) (max∘untag⇑r∙ f)
max∘untag⇑r∙ (foc s q f) = max∘untag⇓r∙ f

max∘untag⇓r∙ (focl q lf (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) refl refl ξ) =
  congfoc (congfocl (max∘untag-lf lf) (congfocr (max∘untag-rf rf) refl))
max∘untag⇓r∙ (focl q lf (focr {Γ₀ = Γ₀} (just x) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) = 
  congfoc (congfocl (max∘untag-lf lf) (congfocr (max∘untag-rf rf) (cong (unfoc {Γ = ∘tcxt Γ₀} ok) (trans (max∘untag⇑ f) (untag-seq≡ {Γ = ∘tcxt Γ₀} {∘tcxt Γ₀} f refl) ))))
max∘untag⇓r∙ (focl {Γ₁ = Γ₁} q lf (unfoc ok f) refl refl ξ) 
  rewrite isProp-isPosAt q (pos→posat ok) =
  trans (cong-only-lf⇑ (max∘untag-lf lf) (max∘untag⇑r∙ f))
        (trans (only-lf⇑≡ {Δ₁ = ∘tcxt Γ₁} {lf = lf} _)
               (only-lf⇑P-r∙ {Δ₁ = untag-cxt Γ₁}{[]} {lf = lf} f _))
max∘untag⇓r∙ (focr {Γ₀ = Γ₀} (just (_ ⊸ _ , _)) rf (unfoc ok f) refl refl ξ) =
  trans (cong-only-rf⇑ (max∘untag-rf rf) (max∘untag⇑l∙ f))
        (only-rf⇑N-l∙ {Δ₀ = untag-cxt Γ₀} {_}{[]} f)
max∘untag⇓r∙ (focr ─ rf (refl , refl) refl refl ξ) =
  congfoc (congfocr (max∘untag-rf rf) refl)

max∘untag⇑l∙ (⊸r f) = cong ⊸r (max∘untag⇑l∙ f)
max∘untag⇑l∙ (foc s q f) = max∘untag⇓l∙ f

max∘untag⇓l∙ (focl q lf (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) refl refl ξ) =
  congfoc (congfocl (max∘untag-lf lf) (congfocr (max∘untag-rf rf) refl))
max∘untag⇓l∙ (focl q lf (focr {Γ₀ = Γ₀} (just x) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) = 
  congfoc (congfocl (max∘untag-lf lf) (congfocr (max∘untag-rf rf) (cong (unfoc {Γ = ∘tcxt Γ₀} ok) (trans (max∘untag⇑ f) (untag-seq≡ {Γ = ∘tcxt Γ₀} {∘tcxt Γ₀} f refl) ))))
max∘untag⇓l∙ (focl {Γ₁ = Γ₁} q lf (unfoc ok f) refl refl ξ)
  rewrite isProp-isPosAt q (pos→posat ok) =
  trans (cong-only-lf⇑ (max∘untag-lf lf) (max∘untag⇑r∙ f))
        (trans (only-lf⇑≡ {Δ₁ = ∘tcxt Γ₁} {lf = lf} _)
               (only-lf⇑P-r∙ {Δ₁ = untag-cxt Γ₁}{[]} {lf = lf} f _))
max∘untag⇓l∙ (focr {Γ₀ = Γ₀} (just (_ ⊸ _ , _)) rf (unfoc ok f) refl refl ξ) =
  trans (cong-only-rf⇑ (max∘untag-rf rf) (max∘untag⇑l∙ f))
        (only-rf⇑N-l∙ {Δ₀ = untag-cxt Γ₀} {_}{[]} f)
max∘untag⇓l∙ (focr ─ rf (refl , refl) refl refl ξ) =
  congfoc (congfocr (max∘untag-rf rf) refl)


max∘untag : ∀ {S Γ A} (f : (∘ , S) MMF.∣ ∘cxt Γ ⇑ (∘ , A)) → max (untag⇑ f) ≡ f
max∘untag {Γ = Γ} f = trans (max∘untag⇑ f) (untag-seq≡ {Γ = ∘cxt Γ}{∘cxt Γ} f refl)

