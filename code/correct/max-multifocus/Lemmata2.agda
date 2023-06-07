{-# OPTIONS --rewriting #-}

module correct.max-multifocus.Lemmata2 where

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

l∙→∘⇑⊸r⋆ : ∀ {S Γ} Δ {C} (f : (∙ , S) MMF.∣ Γ ++ ∙cxt Δ ⇑ (∘ , C))
  → l∙→∘⇑ (MMF.⊸r⋆⇑ Δ f) ≡ MMF.⊸r⋆⇑ Δ (l∙→∘⇑ {Γ = Γ ++ ∙cxt Δ} f)
l∙→∘⇑⊸r⋆ [] f = refl
l∙→∘⇑⊸r⋆ (x ∷ Δ) f = cong ⊸r (l∙→∘⇑⊸r⋆ {Γ = _ ∷ʳ _} Δ f)

only-lf⇑-rf⇑ : ∀ {S} Γ₀ Γ₁ Γ₂ {M Q R} ok
  {s : isIrr S} {r : isPosAt R} {m : isNegAt M} {q : isPosAt Q}
  {lf : r ⇛lf S ∣ Γ₀}
  {rf : just (M , m) MMF.⇛rf Γ₂ ； Q}
  (f : (∘ , just R) MMF.∣ ∘cxt Γ₁ ⇑ (∘ , M)) → 
  only-lf⇑ (∘cxt (Γ₁ ++ Γ₂)) s r lf (only-rf⇑ (∘cxt Γ₁) m q rf f)
    ≡ foc s q (focl {Γ₀ = ∘cxt Γ₀} r lf (focr {Γ₀ = ∘cxt Γ₁}{∘cxt Γ₂} (just (M , m)) rf (unfoc ok f) refl refl tt) refl refl tt)

only-lf⇑P-rf⇑N : ∀ {S S'} Γ Γ₀ Γ₁ Γ₂ Δ {P Q R}
  {s : isIrr S} {p : isPos P} {n : isNeg (Δ ⊸⋆ R)} {q : isPosAt Q}
  {lf : pos→posat p ⇛lf S ∣ Γ₀}
  {rf : just (Δ ⊸⋆ R , neg→negat n) MMF.⇛rf Γ₂ ； Q}
  (f : (∘ , S') MMF.∣ ∘cxt Γ ++ ∘cxt Γ₁ ++ ∘cxt Δ ⇑ (∘ , R)) → 
  (ℓ : MF.L S' Γ P) →
  only-lf⇑P (∘cxt (Γ₁ ++ Γ₂)) s p lf (only-rf⇑N (∘cxt (Γ ++ Γ₁)) Δ n q rf f) ℓ
    ≡ foc s q (focl {Γ₀ = ∘cxt Γ₀} (pos→posat p) lf (focr {Γ₀ = ∘cxt Γ₁} {Γ₁ = ∘cxt Γ₂} (just (Δ ⊸⋆ R , neg→negat n)) rf (unfoc (inj₁ p) (MMF.⊸r⋆⇑ Δ (MMF.runL ℓ f))) refl refl tt) refl refl tt)

only-lf-fP-rf-fN : ∀ {S T Δ'} Γ Γ₀ Γ₁ Γ₂ Δ {P Q R}
  {s : isIrr S} {p : isPos P} {n : isNeg (Δ ⊸⋆ R)} {q : isPosAt Q} {r : isPosAt R}
  {lf : pos→posat p ⇛lf T ∣ Γ₀}
  {rf : just (Δ ⊸⋆ R , neg→negat n) MMF.⇛rf Γ₂ ； Q}
  (f : MMF.[ ∘ , ∘ ] (∘ , S) ∣ Δ' ⇓ (∘ , R))
  (eq : Δ' ≡ ∘cxt Γ ++ ∘cxt Γ₁ ++ ∘cxt Δ) → 
  (ℓ : MF.L S Γ P) →
  only-lf-fP (∘cxt (Γ₁ ++ Γ₂)) s p q lf (only-rf-fN (∘cxt (Γ ++ Γ₁)) Δ s n q r rf f eq) refl ℓ
    ≡ focl {Γ₀ = ∘cxt Γ₀} (pos→posat p) lf (focr {Γ₀ = ∘cxt Γ₁} {Γ₁ = ∘cxt Γ₂} (just (Δ ⊸⋆ R , neg→negat n)) rf (unfoc (inj₁ p) (MMF.⊸r⋆⇑ Δ (MMF.runLQ r ℓ (foc s r (subst⇓ f eq))))) refl refl tt) refl refl tt

only-lf⇑-rf⇑ Γ₀ Γ₁ Γ₂ {` x} {R = I} (inj₁ p) f = {!!}
only-lf⇑-rf⇑ Γ₀ Γ₁ Γ₂ {` x} {R = R ⊗ R₁} (inj₁ p) f = {!!}
only-lf⇑-rf⇑ Γ₀ Γ₁ Γ₂ {M ⊸ M₁} {R = I} (inj₁ p) f = only-lf⇑P-rf⇑N [] Γ₀ Γ₁ Γ₂ [] f done
only-lf⇑-rf⇑ Γ₀ Γ₁ Γ₂ {M ⊸ M₁} {R = R ⊗ R₁} (inj₁ p) f = only-lf⇑P-rf⇑N [] Γ₀ Γ₁ Γ₂ [] f done
only-lf⇑-rf⇑ Γ₀ Γ₁ Γ₂ {M ⊸ M₁} {R = ` X} (inj₂ (x , n)) f = {!!}

only-lf⇑P-rf⇑N Γ Γ₀ Γ₁ Γ₂ Δ (⊸r f) ℓ =
  trans (only-lf⇑P-rf⇑N Γ Γ₀ Γ₁ Γ₂ (Δ ∷ʳ _) f ℓ)
        (congfoc (congfocl refl (congfocr refl (cong (unfoc _) (trans (⊸r⋆⊸r⋆⇑ Δ (_ ∷ []) _) (cong (MMF.⊸r⋆⇑ Δ) (⊸r⋆runL (_ ∷ []) ℓ)))))))
only-lf⇑P-rf⇑N Γ Γ₀ Γ₁ Γ₂ Δ (Il q f) ℓ =
  trans (only-lf⇑P-rf⇑N Γ Γ₀ Γ₁ Γ₂ Δ f (Il-1 ℓ))
        (congfoc (congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ Δ) (cong (MMF.runL ℓ) (Il⇑eq _)))))))
only-lf⇑P-rf⇑N Γ Γ₀ Γ₁ Γ₂ Δ (⊗l q f) ℓ =
  trans (only-lf⇑P-rf⇑N (_ ∷ Γ) Γ₀ Γ₁ Γ₂ Δ f (⊗l-1 ℓ))
        (congfoc (congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ Δ) (cong (MMF.runL ℓ) (⊗l⇑eq _)))))))
only-lf⇑P-rf⇑N Γ Γ₀ Γ₁ Γ₂ Δ {q = q} (foc s _ f) ℓ = 
  congfoc (trans (only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ {q = q} f refl ℓ)
                 (congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ Δ) (sym (runLeq ℓ)))))))

only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₃}{Γ₄} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) eq ℓ with ++? (∘cxt (Γ ++ Γ₁)) Γ₃ (∘cxt Δ) Γ₄ eq
... | inj₂ (A , Ω , refl , eq') with split-map ∘fma Δ (A ∷ Ω) Γ₄ eq'
only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ .((A' ∷ Ω') ++ Γ₄') (focl {_} {_} {_} {_} {.(map _ Γ ++ map _ Γ₁ ++ (∘ , A') ∷ map (λ A → ∘ , A) Ω')} {.(map (λ A → ∘ , A) Γ₄')} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) refl ℓ | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Ω') , refl , eq') | A' ∷ Ω' , Γ₄' , refl , refl , refl 
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt Γ₁) (∘cxt Γ₂) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (l∙→∘⇑⊸r⋆ {Γ = ∘cxt (Γ ++ Γ₁)} (_ ∷ Ω' ++ Γ₄') _))
                    (trans (sym (⊸r⋆runL (_ ∷ Ω' ++ Γ₄') ℓ))
                           (cong (MMF.⊸r⋆⇑ (_ ∷ Ω' ++ Γ₄')) (runLeq ℓ))))))
only-lf-fP-rf-fN {S} Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₃} {Γ₄} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) eq ℓ | inj₁ (Ω , refl , eq') with split-map++ Γ₃ Ω Γ Γ₁ (sym eq')
only-lf-fP-rf-fN {S} _ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = .(map (λ z → ∘ , z) Λ)} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (_ , refl , refl) | inj₁ (Λ , [] , refl , refl , refl) 
  rewrite ++?-alt-eq₁ (∘cxt Λ) (∘cxt Γ₁) (∘cxt Γ₂) | ++?-eq₁ (∘cxt Λ) [] (∘cxt Γ₁) = {!!}
only-lf-fP-rf-fN {S} _ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = .(map (λ z → ∘ , z) Λ)} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (_ , refl , refl) | inj₁ (Λ , A ∷ Λ' , refl , refl , refl) 
  rewrite ++?-alt-eq₁ (∘cxt (Λ ++ A ∷ Λ')) (∘cxt Γ₁) (∘cxt Γ₂) | ++?-alt-eq₂ (∘fma A) (∘cxt Λ) (∘cxt Λ') (∘cxt Γ₁) = {!!}
only-lf-fP-rf-fN {S} Γ Γ₀ .(A ∷ Λ ++ Λ') Γ₂ Δ (focl {Γ₀ = .(map (λ z → ∘ , z) Γ ++ (∘ , A) ∷ map (λ z → ∘ , z) Λ)} {.(map (λ z → ∘ , z) Λ' ++ map _ Δ)} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Λ') , refl , refl) | inj₂ (A , Λ , Λ' , refl , refl , refl)
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt (A ∷ Λ ++ Λ')) (∘cxt Γ₂) | ++?-eq₂ (∘fma A) (∘cxt Γ) (∘cxt Λ) (∘cxt Λ') = {!!}

-- only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₃}{Γ₄} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) eq ℓ with ++?-alt (∘cxt Γ) Γ₃ (∘cxt (Γ₁ ++ Δ)) Γ₄ eq
-- ... | inj₂ (A , Ω , eq' , refl) with split-map ∘fma Γ Γ₃ (A ∷ Ω) eq'
-- only-lf-fP-rf-fN .(Λ ++ A' ∷ Λ') Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = .(map (λ A → ∘ , A) Λ)} {.((∘ , A') ∷ map (λ A → ∘ , A) Λ' ++ map _ Γ₁ ++ map _ Δ)} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) refl ℓ | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Λ') , refl , refl) | Λ , A' ∷ Λ' , refl , refl , refl = {!!}
-- --  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt Δ) = {!++?-alt-eq₂ (∘fma A')!}
-- --    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (cong (MMF.⊸r⋆⇑ Δ) (r∙→∘⇑-runLQ {Δ = ∘cxt (Γ₁ ++ Δ)} ℓ _))))
-- only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = .(map (λ A → ∘ , A) Γ ++ Ω)} {Γ₄} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) eq ℓ | inj₁ (Ω , refl , eq') with split-map++ Ω Γ₄ Γ₁ Δ (sym eq')
-- only-lf-fP-rf-fN Γ Γ₀ .(Λ ++ Λ') Γ₂ Δ (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Λ)} {.(map (λ z → ∘ , z) Λ' ++ map (λ z → ∘ , z) Δ)} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Λ) , refl , refl) | inj₁ (Λ , Λ' , refl , refl , refl)
--   rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt (Λ ++ Λ')) (∘cxt Δ) | ++?-eq₁ (∘cxt Λ) (∘cxt Λ') (∘cxt Δ) = {!!}
-- --    congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ Δ) (only-rf⇑-at-runLQ _ ℓ))))
-- only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ .(A ∷ Λ ++ Λ') (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Γ₁ ++ (∘ , A) ∷ map (λ z → ∘ , z) Λ)} {.(map (λ z → ∘ , z) Λ')} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Γ₁ ++ (∘ , A) ∷ map (λ z → ∘ , z) Λ) , refl , refl) | inj₂ (A , Λ , Λ' , refl , refl , refl)
--   rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt (A ∷ Λ ++ Λ')) | ++?-eq₂ (∘fma A) (∘cxt Γ₁) (∘cxt Λ) (∘cxt Λ') | split-map-eq ∘fma Λ Λ' = {!!}
--    congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ (_ ∷ Λ ++ Λ')) (only-rf⇑-at-runLQ _ ℓ))))

-- only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₅} q lf (focr {Γ₀ = Γ₃}{Γ₄} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ with ++?-alt (∘cxt Γ) (Γ₅ ++ Γ₃) (∘cxt (Γ₁ ++ Δ)) Γ₄ eq
-- ... | inj₂ (A , Ω , eq' , refl) with split-map ∘fma Γ Γ₅ (Γ₃ ++ A ∷ Ω) eq'
-- ... | Ξ , Ξ' , refl , eq₀ , refl with split-map ∘fma Ξ' Γ₃ (_ ∷ Ω) eq₀
-- only-lf-fP-rf-fN .(Ξ ++ Γ₃' ++ A' ∷ Ω') Γ₀ Γ₁ Γ₂ Δ (focl {_} {_} {_} {_} {.(map _ Ξ)} q lf (focr {Γ₀ = .(map (λ A → ∘ , A) Γ₃')} {.((∘ , A') ∷ map (λ A → ∘ , A) Ω' ++ map _ Γ₁ ++ map _ Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Ω') , eq' , refl) | Ξ , .(Γ₃' ++ A' ∷ Ω') , refl , eq₀ , refl | Γ₃' , A' ∷ Ω' , refl , refl , refl
--   rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt Δ) = {!!}
-- --    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (cong (MMF.⊸r⋆⇑ Δ) (r∙→∘⇑-runLQ {Δ = ∘cxt (Γ₁ ++ Δ)} ℓ _))))
-- only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₅} q lf (focr {Γ₀ = Γ₃}{Γ₄} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ | inj₁ (Ω , eq' , eq'') with ++?-alt (∘cxt Γ) Γ₅ Ω Γ₃ eq'
-- ... | inj₂ (A , Ω , eq₀ , refl) with split-map ∘fma Γ Γ₅ (_ ∷ Ω) eq₀
-- only-lf-fP-rf-fN .(Γ₅' ++ A' ∷ Ω') Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₅')} q lf (focr {_} {_} {_} {_} {_} {.((∘ , A') ∷ map (λ A → ∘ , A) Ω' ++ Ω)} {Γ₄} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ | inj₁ (Ω , refl , eq'') | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Ω') , eq₀ , refl) | Γ₅' , A' ∷ Ω' , refl , refl , refl with split-map++ Ω Γ₄ Γ₁ Δ (sym eq'')
-- only-lf-fP-rf-fN .(Γ₅' ++ A' ∷ Ω') Γ₀ .(Ξ ++ Ξ') Γ₂ Δ {r = r} (focl {_} {_} {_} {_} {.(map _ Γ₅')} q lf (focr {_} {_} {_} {_} {_} {.((∘ , A') ∷ map _ Ω' ++ map (λ z → ∘ , z) Ξ)} {.(map (λ z → ∘ , z) Ξ' ++ map (λ z → ∘ , z) Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Ξ) , refl , refl) | inj₂ (.(∘ , A') , .(map _ Ω') , eq₀ , refl) | Γ₅' , A' ∷ Ω' , refl , refl , refl | inj₁ (Ξ , Ξ' , refl , refl , refl)
--   rewrite ++?-alt-eq₂ (∘fma A') (∘cxt Γ₅') (∘cxt Ω') (∘cxt Ξ) | split-map-eq ∘fma Γ₅' (A' ∷ Ω') | ++?-eq₁ (∘cxt Γ₀) (∘cxt (Ξ ++ Ξ')) (∘cxt Δ) | ++?-eq₁ (∘cxt Ξ) (∘cxt Ξ') (∘cxt Δ) = {!!}
-- --    congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ Δ)
-- --      (trans (only-rf⇑-runL (only-lf⇑ (∘cxt (A' ∷ Ω' ++ Ξ)) _ q lf f) ℓ)
-- --             (cong (MMF.runLQ r ℓ) (only-rf⇑-lf⇑ Γ₅' (_ ∷ Ω' ++ Ξ) (Ξ' ++ Δ) ok f))))))  
-- only-lf-fP-rf-fN .(Γ₅' ++ A' ∷ Ω') Γ₀ Γ₁ Γ₂ .(A'' ∷ Ξ ++ Ξ') {s = s} {r = r} (focl {_} {_} {_} {_} {.(map _ Γ₅')} q lf (focr {_} {_} {_} {_} {_} {.((∘ , A') ∷ map _ Ω' ++ map (λ z → ∘ , z) Γ₁ ++ (∘ , A'') ∷ map (λ z → ∘ , z) Ξ)} {.(map (λ z → ∘ , z) Ξ')} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Γ₁ ++ (∘ , A'') ∷ map (λ z → ∘ , z) Ξ) , refl , refl) | inj₂ (.(∘ , A') , .(map _ Ω') , eq₀ , refl) | Γ₅' , A' ∷ Ω' , refl , refl , refl | inj₂ (A'' , Ξ , Ξ' , refl , refl , refl)
--   rewrite ++?-alt-eq₂ (∘fma A') (∘cxt Γ₅') (∘cxt Ω') (∘cxt (Γ₁ ++ A'' ∷ Ξ)) | split-map-eq ∘fma Γ₅' (A' ∷ Ω') | ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt (A'' ∷ Ξ ++ Ξ')) | ++?-eq₂ (∘fma A'') (∘cxt Γ₁) (∘cxt Ξ) (∘cxt Ξ') | split-map-eq ∘fma Ξ Ξ' = {!!}
-- --    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (cong (MMF.⊸r⋆⇑ (_ ∷ Ξ ++ Ξ'))
-- --      (trans (only-rf⇑-runL {Δ₀ = ∘cxt (Γ₁ ++ A'' ∷ Ξ)} (only-lf⇑ (∘cxt (A' ∷ Ω' ++ Γ₁ ++ A'' ∷ Ξ)) _ q lf f) ℓ)
-- --             (cong (MMF.runLQ r ℓ) (only-rf⇑-lf⇑ Γ₅' (A' ∷ Ω' ++ Γ₁ ++ A'' ∷ Ξ) Ξ' ok f))))))
-- only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = .(map (λ A → ∘ , A) Γ ++ Λ)} q lf (focr {Γ₀ = Γ₃} {Γ₄} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ | inj₁ (.(Λ ++ Γ₃) , refl , eq'') | inj₁ (Λ , refl , refl) with split-map++₂ Λ Γ₃ Γ₄ Γ₁ Δ (sym eq'')
-- only-lf-fP-rf-fN Γ Γ₀ .(Ξ ++ Ξ' ++ Ξ'') Γ₂ Δ {r = r} (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Ξ)} q lf (focr {Γ₀ = .(map (λ z → ∘ , z) Ξ')} {.(map (λ z → ∘ , z) Ξ'' ++ map (λ z → ∘ , z) Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Ξ ++ map (λ z → ∘ , z) Ξ') , refl , refl) | inj₁ (.(map (λ z → ∘ , z) Ξ) , refl , refl) | inj₁ (Ξ , Ξ' , Ξ'' , refl , refl , refl , refl)
--   rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt Ξ) (∘cxt Ξ') | ++?-eq₁ (∘cxt Γ₀) (∘cxt (Ξ ++ Ξ' ++ Ξ'')) (∘cxt Δ) | ++?-eq₁ (∘cxt (Ξ ++ Ξ')) (∘cxt Ξ'') (∘cxt Δ) = {!!}
-- --     congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ Δ)
-- --       (trans (only-rf⇑-runL (only-lf⇑ (∘cxt Ξ') _ q lf f) ℓ) 
-- --              (cong (MMF.runLQ r ℓ) (only-rf⇑-lf⇑ (Γ ++ Ξ) Ξ' (Ξ'' ++ Δ) ok f))))))
-- only-lf-fP-rf-fN Γ Γ₀ .(Ξ ++ Ξ') Γ₂ .(A' ∷ Ξ'' ++ Ξ''') {s = s} {r = r} (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Ξ)} q lf (focr {Γ₀ = .(map (λ z → ∘ , z) Ξ' ++ (∘ , A') ∷ map (λ z → ∘ , z) Ξ'')} {.(map (λ z → ∘ , z) Ξ''')} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Ξ ++ map (λ z → ∘ , z) Ξ' ++ (∘ , A') ∷ map (λ z → ∘ , z) Ξ'') , refl , refl) | inj₁ (.(map (λ z → ∘ , z) Ξ) , refl , refl) | inj₂ (inj₁ (Ξ , Ξ' , A' , Ξ'' , Ξ''' , refl , refl , refl , refl , refl))
--   rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt Ξ) (∘cxt (Ξ' ++ A' ∷ Ξ'')) | ++?-eq₁ (∘cxt Γ₀) (∘cxt (Ξ ++ Ξ')) (∘cxt (A' ∷ Ξ'' ++ Ξ''')) | ++?-eq₂ (∘fma A') (∘cxt (Ξ ++ Ξ')) (∘cxt Ξ'') (∘cxt Ξ''') | split-map-eq ∘fma Ξ'' Ξ''' = {!!}
-- --     congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (Ξ ++ Ξ')} _) (cong (MMF.⊸r⋆⇑ {Γ = ∘cxt (Ξ ++ Ξ')} (_ ∷ Ξ'' ++ Ξ'''))
-- --       (trans (only-rf⇑-runL {Δ₀ = ∘cxt (Ξ ++ Ξ' ++ _ ∷ Ξ'')}{Ξ'''} (only-lf⇑ {Δ₀ = Γ ++ Ξ} (∘cxt (Ξ' ++ A' ∷ Ξ'')) s q lf f) ℓ)
-- --              (cong (MMF.runLQ r ℓ) (only-rf⇑-lf⇑ (Γ ++ Ξ) (Ξ' ++ _ ∷ Ξ'') Ξ''' ok f))))))
-- only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ .(A' ∷ Ξ ++ Ξ' ++ Ξ'') {r = r} (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Γ₁ ++ (∘ , A') ∷ map (λ z → ∘ , z) Ξ)} q lf (focr {Γ₀ = .(map (λ z → ∘ , z) Ξ')} {.(map (λ z → ∘ , z) Ξ'')} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.((map (λ z → ∘ , z) Γ₁ ++ (∘ , A') ∷ map (λ z → ∘ , z) Ξ) ++ map (λ z → ∘ , z) Ξ') , refl , refl) | inj₁ (.(map (λ z → ∘ , z) Γ₁ ++ (∘ , A') ∷ map (λ z → ∘ , z) Ξ) , refl , refl) | inj₂ (inj₂ (A' , Ξ , Ξ' , Ξ'' , refl , refl , refl , refl))
--   rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt (Γ₁ ++ A' ∷ Ξ)) (∘cxt Ξ') | ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt (A' ∷ Ξ ++ Ξ' ++ Ξ'')) | ++?-eq₂ (∘fma A') (∘cxt Γ₁) (∘cxt (Ξ ++ Ξ')) (∘cxt Ξ'') | split-map-eq ∘fma (Ξ ++ Ξ') Ξ'' = {!!}
-- --     congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (cong (MMF.⊸r⋆⇑ (_ ∷ Ξ ++ Ξ' ++ Ξ''))
-- --       (trans (only-rf⇑-runL {Δ₀ = ∘cxt (Γ₁ ++ A' ∷ Ξ ++ Ξ')} (only-lf⇑ (∘cxt Ξ') _ q lf f) ℓ) 
-- --              (cong (MMF.runLQ r ℓ) (only-rf⇑-lf⇑ (Γ ++ Γ₁ ++ _ ∷ Ξ) Ξ' Ξ'' ok f)))))) 

-- only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₃}{Γ₄} q lf (unfoc ok f) refl refl ξ) eq ℓ with ++?-alt (∘cxt Γ) Γ₃ (∘cxt (Γ₁ ++ Δ)) Γ₄ eq
-- ... | inj₁ (Λ , refl , eq') with split-map++ Λ Γ₄ Γ₁ Δ (sym eq')
-- only-lf-fP-rf-fN Γ Γ₀ .(Ω ++ Ω') Γ₂ Δ {s = s}{r = r} (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Ω)} {.(map (λ z → ∘ , z) Ω' ++ map (λ z → ∘ , z) Δ)} q lf (unfoc ok f) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Ω) , refl , refl) | inj₁ (Ω , Ω' , refl , refl , refl)
--   rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt (Ω ++ Ω')) (∘cxt Δ) | r∙→∘⇑-runLQ {Γ = Γ}{∘cxt (Ω ++ Ω' ++ Δ)} {q = r} ℓ (foc s r (focl {Γ₀ = ∙cxt Γ ++ ∘cxt Ω}{∘cxt (Ω' ++ Δ)} q lf (unfoc ok f) refl refl tt)) = {!!}
--   --refl 
-- only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ .(A' ∷ Ω ++ Ω') (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Γ₁ ++ (∘ , A') ∷ map (λ z → ∘ , z) Ω)} {.(map (λ z → ∘ , z) Ω')} q lf (unfoc ok f) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Γ₁ ++ (∘ , A') ∷ map (λ z → ∘ , z) Ω) , refl , refl) | inj₂ (A' , Ω , Ω' , refl , refl , refl)
--   rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt (A' ∷ Ω ++ Ω')) = {!!}
-- --    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (cong (MMF.⊸r⋆⇑ (_ ∷ Ω ++ Ω')) (r∙→∘⇑-runLQ {Δ = ∘cxt (Γ₁ ++ A' ∷ Ω ++ Ω')} ℓ _))))
-- only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₃} {.(A ∷ Λ ++ map (λ z → ∘ , z) Γ₁ ++ map (λ z → ∘ , z) Δ)} q lf (unfoc ok f) refl refl ξ) eq ℓ | inj₂ (A , Λ , eq' , refl) with split-map ∘fma Γ Γ₃ (_ ∷ Λ) eq'
-- only-lf-fP-rf-fN .(Γ₃' ++ A' ∷ Λ') Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₃')} {.((∘ , A') ∷ map (λ A → ∘ , A) Λ' ++ map _ Γ₁ ++ map _ Δ)} q lf (unfoc ok f) refl refl ξ) refl ℓ | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Λ') , refl , refl) | Γ₃' , A' ∷ Λ' , refl , refl , refl
--   rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt Δ) = {!!}
-- --    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁}_) (cong (MMF.⊸r⋆⇑ Δ) (r∙→∘⇑-runLQ {Δ = ∘cxt (Γ₁ ++ Δ)} ℓ _))))

-- only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focr {Γ₀ = Γ₃} {Γ₄} (just (M , m)) rf (unfoc ok f) refl refl ξ) eq ℓ with ++?-alt (∘cxt Γ) Γ₃ (∘cxt (Γ₁ ++ Δ)) Γ₄ eq
-- ... | inj₁ (Λ , refl , eq') with split-map++ Λ Γ₄ Γ₁ Δ (sym eq')
-- only-lf-fP-rf-fN Γ Γ₀ .(Ω ++ Ω') Γ₂ Δ (focr {_} {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Ω)} {.(map (λ z → ∘ , z) Ω' ++ map (λ z → ∘ , z) Δ)} (just (M ⊸ M' , m)) rf (unfoc ok f) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Ω) , refl , refl) | inj₁ (Ω , Ω' , refl , refl , refl)
--   rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt (Ω ++ Ω')) (∘cxt Δ) | ++?-eq₁ (∘cxt Ω) (∘cxt Ω') (∘cxt Δ) = {!!}
-- --     congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (Ω ++ Ω')} _) (cong (MMF.⊸r⋆⇑ {Γ = ∘cxt (Ω ++ Ω')} Δ)
-- --       (trans (only-rf⇑-runL (l∙→∘⇑ f) ℓ) 
-- --              (cong (MMF.runLQ _ ℓ) (only-rf⇑N-l∙ {Δ₀ = Γ ++ Ω}{Ω' ++ Δ}{[]} f))))))
-- only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ .(A ∷ Ω ++ Ω') (focr {_} {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Γ₁ ++ (∘ , A) ∷ map (λ z → ∘ , z) Ω)} {.(map (λ z → ∘ , z) Ω')} (just (M ⊸ M' , m)) rf (unfoc ok f) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Γ₁ ++ (∘ , A) ∷ map (λ z → ∘ , z) Ω) , refl , refl) | inj₂ (A , Ω , Ω' , refl , refl , refl)
--   rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt (A ∷ Ω ++ Ω')) | ++?-eq₂ (∘fma A) (∘cxt Γ₁) (∘cxt Ω) (∘cxt Ω') | split-map-eq ∘fma Ω Ω' = {!!}
-- --     congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ (_ ∷ Ω ++ Ω'))
-- --       (trans (only-rf⇑-runL (l∙→∘⇑ f)  ℓ)
-- --              (cong (MMF.runLQ _ ℓ) (only-rf⇑N-l∙ {Δ₀ = Γ ++ Γ₁ ++ A ∷ Ω}{Ω'}{[]} f))))))
-- only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focr {Γ₀ = Γ₃} {.(A ∷ Λ ++ map (λ z → ∘ , z) Γ₁ ++ map (λ z → ∘ , z) Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ) eq ℓ | inj₂ (A , Λ , eq' , refl) with split-map ∘fma Γ Γ₃ (A ∷ Λ) eq'
-- only-lf-fP-rf-fN .(Γ₃' ++ A' ∷ Λ') Γ₀ Γ₁ Γ₂ Δ (focr {Γ₀ = .(map (λ A → ∘ , A) Γ₃')} {.((∘ , A') ∷ map (λ A → ∘ , A) Λ' ++ map _ Γ₁ ++ map _ Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ) refl ℓ | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Λ') , refl , refl) | Γ₃' , A' ∷ Λ' , refl , refl , refl
--   rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt Δ) = {!!}
-- --    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (cong (MMF.⊸r⋆⇑ Δ) (r∙→∘⇑-runLQ {Δ = ∘cxt (Γ₁ ++ Δ)} ℓ _))))
-- only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focr ─ rf (refl , refl) refl refl ξ) refl ℓ
--   rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt Δ) = {!!}
-- --    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (cong (MMF.⊸r⋆⇑ Δ) (r∙→∘⇑-runLQ {Δ = ∘cxt (Γ₁ ++ Δ)} ℓ _))))
