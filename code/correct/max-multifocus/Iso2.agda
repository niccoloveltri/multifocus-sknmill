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
--open import correct.multifocus.EqComplete


untag⇑∘max : ∀ {S Γ A} (f : S MF.∣ Γ ⇑ A) → untag⇑ (max f) ≗⇑ f

untag⇑∘max (⊸r f) = ⊸r (untag⇑∘max f)
untag⇑∘max (Il q f) = Il (untag⇑∘max f)
untag⇑∘max (⊗l q f) = ⊗l (untag⇑∘max f)
untag⇑∘max (foc s q (focl q₁ lf (focr (just (.(` _) , snd)) rf ax refl) refl)) = foc (focl {!!} (focr {!!} refl))
untag⇑∘max (foc s q (focl q₁ lf (focr (just x) rf (unfoc ok f) refl) refl)) = foc (focl {!!} (focr {!!} (unfoc (untag⇑∘max f))))
untag⇑∘max (foc s q (focl q₁ lf (unfoc ok f) refl)) = {!!}
untag⇑∘max (foc s q (focr (just (.(` _) , snd)) rf (focl q₁ lf ax refl) refl)) = foc (swap • focr {!!} (focl {!!} refl))
untag⇑∘max (foc s q (focr (just x) rf (focl q₁ lf (unfoc ok f) refl) refl)) = foc (swap • focr {!!} (focl {!!} (unfoc (untag⇑∘max f))))
untag⇑∘max (foc s q (focr (just x) rf (unfoc ok f) refl)) = {!!}
untag⇑∘max (foc s q (focr ─ rf (refl , refl) refl)) = foc (focrn {!!})
