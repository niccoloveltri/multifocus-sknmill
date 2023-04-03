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
--open import correct.multifocus.EqComplete


max∘untag⇑ : ∀ {S Γ A} (f : (∘ , S) MMF.∣ ∘cxt Γ ⇑ (∘ , A)) → max (untag⇑ f) ≡ f
max∘untag⇓ : ∀ {S Γ A s q} (f : MMF.[ ∘ , ∘ ] (∘ , S) ∣ ∘cxt Γ ⇓ (∘ , A))
  → max (foc s q (untag⇓ f)) ≡ foc s q f
-- max∘untag⇑r∙ : ∀ {S Γ A} (f : (∘ , S) MMF.∣ ∘cxt Γ ⇑ (∙ , A))
--   → max (untag⇑ f) ≡ r∙→∘⇑ {Γ = ∘cxt Γ} f

max∘untag⇑ {Γ = Γ} (⊸r f) = cong ⊸r (max∘untag⇑ {Γ = Γ ∷ʳ _} f)
max∘untag⇑ (Il q f) = cong (Il q) (max∘untag⇑ f)
max∘untag⇑ (⊗l q f) = cong (⊗l q) (max∘untag⇑ f)
max∘untag⇑ (foc s q f) = max∘untag⇓ f

max∘untag⇓ {Γ = Γ} (focl {Γ₀ = Γ₀} {Γ₁} q lf (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) eq refl ξ) with split-map ∘fma Γ Γ₀ Γ₁ eq
max∘untag⇓ {Γ = .(Γ₀ ++ Γ₁)} (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₀)} {.(map (λ A → ∘ , A) Γ₁)} q lf (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) refl refl ξ) | Γ₀ , Γ₁ , refl , refl , refl =
  congfoc (congfocl {!!} (congfocr {!!} refl))
max∘untag⇓ {Γ = Γ} (focl {Γ₀ = Γ₂} q lf (focr {Γ₀ = Γ₀} {Γ₁} (just x) rf (unfoc ok f) refl refl ξ₁) eq refl ξ) with split-map ∘fma Γ Γ₂ (Γ₀ ++ Γ₁) eq
... | Γ₂ , Γ' , refl , eq' , refl with split-map ∘fma Γ' Γ₀ Γ₁ eq'
max∘untag⇓ {_} {.(Γ₂ ++ Γ₀ ++ Γ₁)} (focl {_} {_} {_} {_} {.(map _ Γ₂)} q lf (focr {Γ₀ = .(map (λ A → ∘ , A) Γ₀)} {.(map (λ A → ∘ , A) Γ₁)} (just x) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) | Γ₂ , .(Γ₀ ++ Γ₁) , refl , eq' , refl | Γ₀ , Γ₁ , refl , refl , refl =
  congfoc (congfocl {!!} (congfocr {!!} (cong (unfoc {Γ = ∘cxt Γ₀} ok) (max∘untag⇑ f))))
max∘untag⇓ {Γ = Γ} (focl {Γ₀ = Γ₀} {Γ₁} q lf (unfoc ok f) eq refl ξ) with split-map ∘fma Γ Γ₀ Γ₁ eq
max∘untag⇓ {Γ = .(Γ₀ ++ Γ₁)} (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₀)} {.(map (λ A → ∘ , A) Γ₁)} q lf (unfoc ok f) refl refl ξ) | Γ₀ , Γ₁ , refl , refl , refl = {!!}
max∘untag⇓ {Γ = Γ} (focr {Γ₀ = Γ₀} {Γ₁} (just x) rf (unfoc ok f) eq refl ξ) with split-map ∘fma Γ Γ₀ Γ₁ eq
max∘untag⇓ {Γ = .(Γ₀ ++ Γ₁)} (focr {Γ₀ = .(map (λ A → ∘ , A) Γ₀)} {.(map (λ A → ∘ , A) Γ₁)} (just x) rf (unfoc ok f) refl refl ξ) | Γ₀ , Γ₁ , refl , refl , refl = {!!}
max∘untag⇓ (focr ─ rf (refl , refl) refl refl ξ) = congfoc (congfocr {!!} refl)
