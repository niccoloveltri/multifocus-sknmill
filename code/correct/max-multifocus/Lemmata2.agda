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

only-lf-f-rf-f-at : ∀ {S S' Γ} Γ₀ Γ₁ Γ₂ {X P Q}
  {s : isIrr S'} {x : isAt X} {p : isPos P} {q : isPosAt Q} 
  {lf : pos→posat p ⇛lf S ∣ Γ₀}
  {rf : just (X , at→negat x) MMF.⇛rf Γ₂ ； Q}
  (f : MMF.[ ∘ , ∘ ] (∘ , S') ∣ ∘cxt Γ ++ ∘cxt Γ₁ ⇓ (∘ , X))
  (ℓ : L S' Γ P) → 
  only-lf-fP (∘cxt (Γ₁ ++ Γ₂)) s p q lf (only-rf-f-at (∘cxt (Γ ++ Γ₁)) x q rf f) refl ℓ
    ≡ focl {Γ₀ = ∘cxt Γ₀} (pos→posat p) lf (focr {Γ₀ = ∘cxt Γ₁} {Γ₁ = ∘cxt Γ₂} _ rf (unfoc (inj₁ p) (MMF.runLQ (at→posat x) ℓ (foc s (at→posat x) f))) refl refl tt) refl refl tt
only-lf-f-rf-f-at Γ₀ Γ₁ Γ₂ {x = x} (focl q lf (focr s (⊗r+ Δ₀ Ξ m rf gs) f eq₁ eq'' ξ₁) eq eq' ξ) ℓ =
  ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (map proj₂ Ξ)) (at→negat x))
only-lf-f-rf-f-at {Γ = Γ} Γ₀ Γ₁ Γ₂ {` X} (focl q lf (focr {Γ₁ = []} (just _) blurr ax refl refl ξ₁) refl refl ξ) ℓ 
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt Γ₁) (∘cxt Γ₂) = refl
only-lf-f-rf-f-at {Γ = Γ} Γ₀ Γ₁ Γ₂ {` X} (focl {Γ₀ = Γ₃} {Γ₄} q lf (focr {Γ₁ = []} (just _) blurr (unfoc (inj₁ p) f) refl refl ξ₁) eq refl ξ) ℓ with split-map++ Γ₃ Γ₄ Γ Γ₁ (sym eq)
only-lf-f-rf-f-at Γ₀ Γ₁ Γ₂ {` X} (focl {Γ₀ = .(map (λ A → ∘ , A) Ω)} q lf (focr {_} {_} {_} {_} {_} {_} {[]} (just .(` X , _)) blurr (unfoc (inj₁ p) f) refl refl ξ₁) refl refl ξ) ℓ | inj₁ (Ω , [] , refl , refl , refl)
  rewrite ++?-alt-eq₁ (∘cxt Ω) (∘cxt Γ₁) (∘cxt Γ₂) | ++?-alt-eq₁ (∘cxt Ω) [] (∘cxt Γ₁) | isProp-isPosAt q (pos→posat p) = 
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _)
             (trans (runLeq ℓ)
                    (cong (MMF.runLQ tt ℓ) (trans (only-lf⇑≡ {lf = lf} _)
                                                  (trans (only-lf⇑P-at≡ (∘cxt Γ₁) _ _ _ f done)
                                                         (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (untag-seq≡ {Γ = ∘cxt Γ₁} f refl )))))))))))
only-lf-f-rf-f-at Γ₀ Γ₁ Γ₂ {` X} (focl {Γ₀ = .(map (λ A → ∘ , A) Ω)} q lf (focr {_} {_} {_} {_} {_} {_} {[]} (just .(` X , _)) blurr (unfoc (inj₁ p) f) refl refl ξ₁) refl refl ξ) ℓ | inj₁ (Ω , A ∷ Ω' , refl , refl , refl)
  rewrite ++?-alt-eq₁ (∘cxt (Ω ++ A ∷ Ω')) (∘cxt Γ₁) (∘cxt Γ₂) | ++?-eq₁ (∘cxt Ω) (∘cxt (A ∷ Ω')) (∘cxt Γ₁) | split-map-eq ∘fma Ω (A ∷ Ω') | isProp-isPosAt q (pos→posat p) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _)
             (trans (runLeq ℓ)
                    (cong (MMF.runLQ tt ℓ) (trans (only-lf⇑≡ {lf = lf} _)
                                                  (trans (only-lf⇑P-at≡ (∘cxt (A ∷ Ω' ++ Γ₁)) _ _ _ f done)
                                                         (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (A ∷ Ω' ++ Γ₁)} _) (untag-seq≡ {Γ = ∘cxt (A ∷ Ω' ++ Γ₁)} f refl )))))))))))
only-lf-f-rf-f-at {Γ = Γ} Γ₀ .(A ∷ Ω ++ Ω') Γ₂ {` X} (focl {Γ₀ = .(map (λ z → ∘ , z) Γ ++ (∘ , A) ∷ map (λ z → ∘ , z) Ω)} {.(map (λ A₁ → ∘ , A₁) Ω')} q lf (focr {_} {_} {_} {_} {_} {_} {[]} (just .(` X , _)) blurr (unfoc (inj₁ p) f) refl refl ξ₁) refl refl ξ) ℓ | inj₂ (A , Ω , Ω' , refl , refl , refl)
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt (A ∷ Ω ++ Ω')) (∘cxt Γ₂) | ++?-alt-eq₁ (∘cxt Γ) (∘cxt (A ∷ Ω)) (∘cxt Ω') | isProp-isPosAt q (pos→posat p) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (A ∷ Ω ++ Ω')} _)
             (trans (runLeq ℓ)
                    (cong (MMF.runLQ tt ℓ) (trans (only-lf⇑≡ {lf = lf} _)
                                                  (trans (only-lf⇑P-at≡ (∘cxt Ω') _ _ lf f done)
                                                         (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Ω'} _) (untag-seq≡ {Γ = ∘cxt Ω'} f refl)))))))))))
only-lf-f-rf-f-at Γ₀ Γ₁ Γ₂ {x = x} (focl q lf (unfoc ok f) eq eq' ξ) ℓ = ⊥-elim (∙r⇑-at x f)
only-lf-f-rf-f-at Γ₀ Γ₁ Γ₂ {x = x} (focr s (⊗r+ Δ₀ Ξ m rf gs) f eq eq' ξ) ℓ =
  ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (map proj₂ Ξ)) (at→negat x))
only-lf-f-rf-f-at Γ₀ Γ₁ Γ₂ {` X} (focr {Γ₁ = []} (just _) blurr (unfoc () f) refl refl ξ) ℓ

only-lf⇑P-rf⇑-at : ∀ {S' S Γ} Γ₀ Γ₁ Γ₂ {X Q P} 
  {s : isIrr S} {p : isPos P} {x : isAt X} {q : isPosAt Q}
  {lf : pos→posat p ⇛lf S ∣ Γ₀}
  {rf : just (X , at→negat x) MMF.⇛rf Γ₂ ； Q}
  (f : (∘ , S') MMF.∣ ∘cxt (Γ ++ Γ₁) ⇑ (∘ , X))
  (ℓ : L S' Γ P) → 
  only-lf⇑P (∘cxt (Γ₁ ++ Γ₂)) s p lf (only-rf⇑-at (∘cxt (Γ ++ Γ₁)) x q rf f) ℓ
    ≡ foc s q (focl {Γ₀ = ∘cxt Γ₀} (pos→posat p) lf (focr {Γ₀ = ∘cxt Γ₁} {∘cxt Γ₂} (just _) rf (unfoc (inj₁ p) (MMF.runLQ (at→posat x) ℓ f)) refl refl tt) refl refl tt)
only-lf⇑P-rf⇑-at Γ₀ Γ₁ Γ₂ {x = x} (Il q f) ℓ rewrite isProp-isPosAt q (at→posat x) =
  only-lf⇑P-rf⇑-at Γ₀ Γ₁ Γ₂ f (Il-1 ℓ)
only-lf⇑P-rf⇑-at Γ₀ Γ₁ Γ₂ {x = x} (⊗l q f) ℓ rewrite isProp-isPosAt q (at→posat x) =
  only-lf⇑P-rf⇑-at Γ₀ Γ₁ Γ₂ f (⊗l-1 ℓ)
only-lf⇑P-rf⇑-at Γ₀ Γ₁ Γ₂ {x = x} (foc s q f) ℓ rewrite isProp-isPosAt q (at→posat x) =
  congfoc (only-lf-f-rf-f-at Γ₀ Γ₁ Γ₂ f ℓ)


only-lf-f-rf-fN : ∀ {S} Γ₀ Γ₁ Γ₂ Δ {X Q R}
  {s : isIrr S} {x : isAt X} {n : isNeg (Δ ⊸⋆ R)} {q : isPosAt Q} {r : isPosAt R}
  {lf : at→posat x ⇛lf S ∣ Γ₀}
  {rf : just (Δ ⊸⋆ R , neg→negat n) MMF.⇛rf Γ₂ ； Q}
  (f : MMF.[ ∘ , ∘ ] (∘ , just X) ∣ ∘cxt Γ₁ ++ ∘cxt Δ ⇓ (∘ , R)) → 
  only-lf-f-at (∘cxt (Γ₁ ++ Γ₂)) s x lf (only-rf-fN (∘cxt Γ₁) Δ (at→negat x) n q r rf f refl)  
    ≡ focl {Γ₀ = ∘cxt Γ₀} (at→posat x) lf (focr {Γ₀ = ∘cxt Γ₁} {Γ₁ = ∘cxt Γ₂} (just (Δ ⊸⋆ R , neg→negat n)) rf (unfoc (inj₂ (x , n)) (MMF.⊸r⋆⇑ Δ (foc (at→negat x) r f))) refl refl tt) refl refl tt
only-lf-f-rf-fN Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = []} q blurl (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) refl refl ξ)
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt Δ) = refl
only-lf-f-rf-fN Γ₀ Γ₁ Γ₂ Δ {X = ` X} (focl {Γ₀ = []} q blurl (focr {Γ₀ = Λ₀}{Λ₁} (just x) rf (unfoc (inj₂ (_ , n)) f) refl refl ξ₁) eq refl ξ) with ++?-alt Λ₀ (∘cxt Γ₁) Λ₁ (∘cxt Δ) eq
... | inj₁ (Ω , eq' , refl) with split-map ∘fma Γ₁ Λ₀ Ω eq'
only-lf-f-rf-fN Γ₀ .(Λ₀ ++ Ω) Γ₂ Δ (focl {_} {_} {_} {_} {[]} q blurl (focr {Γ₀ = .(map (λ A → ∘ , A) Λ₀)} {.(map (λ A → ∘ , A) Ω ++ map _ Δ)} (just (_ ⊸ _ , m)) rf (unfoc (inj₂ (_ , n)) f) refl refl ξ₁) refl refl ξ) | inj₁ (.(map (λ A → ∘ , A) Ω) , eq' , refl) | Λ₀ , Ω , refl , refl , refl
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt (Λ₀ ++ Ω)) (∘cxt Δ) | ++?-eq₁ (∘cxt Λ₀) (∘cxt Ω) (∘cxt Δ) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (Λ₀ ++ Ω)} _) (cong (MMF.⊸r⋆⇑ Δ)
      (trans (only-rf⇑N-at≡ (∘cxt Λ₀) [] tt _ _ f)
             (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Λ₀} _) (untag-seq≡ {Γ = ∘cxt Λ₀}{∘cxt Λ₀} _ refl)))))))))
only-lf-f-rf-fN {S} Γ₀ Γ₁ Γ₂ Δ (focl {_} {_} {_} {_} {[]} q blurl (focr {Γ₀ = .(map (λ A₁ → ∘ , A₁) Γ₁ ++ A ∷ Ω)} {Λ₁} (just (_ ⊸ _ , m)) rf (unfoc (inj₂ (_ , n)) f) refl refl ξ₁) eq refl ξ) | inj₂ (A , Ω , refl , eq') with split-map ∘fma Δ (_ ∷ Ω) Λ₁ eq'
only-lf-f-rf-fN {S} Γ₀ Γ₁ Γ₂ .((_ ∷ Ω') ++ Λ₁') {` _} (focl {_} {_} {_} {_} {[]} q blurl (focr {_} {_} {_} {_} {_} {.(map _ Γ₁ ++ (∘ , _) ∷ map (λ A → ∘ , A) Ω')} {.(map (λ A → ∘ , A) Λ₁')} (just x) rf (unfoc (inj₂ (_ , n)) f) refl refl ξ₁) refl refl ξ) | inj₂ (.(∘ , _) , .(map (λ A → ∘ , A) Ω') , refl , eq') | A' ∷ Ω' , Λ₁' , refl , refl , refl
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt (A' ∷ Ω' ++ Λ₁')) | ++?-eq₂ (∘fma A') (∘cxt Γ₁) (∘cxt Ω') (∘cxt Λ₁') | split-map-eq ∘fma Ω' Λ₁' =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (cong (MMF.⊸r⋆⇑ (_ ∷ Ω' ++ Λ₁'))
      (trans (only-rf⇑N-at≡ (∘cxt (Γ₁ ++ _ ∷ Ω')) [] tt _ _ f)
             (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (Γ₁ ++ _ ∷ Ω')} _) (untag-seq≡ {Γ = ∘cxt (Γ₁ ++ _ ∷ Ω')}{∘cxt (Γ₁ ++ _ ∷ Ω')} _ refl)))))))))
only-lf-f-rf-fN Γ₀ Γ₁ Γ₂ Δ {X = ` X} (focl {Γ₀ = []} q blurl (unfoc () f) eq refl ξ) 
only-lf-f-rf-fN Γ₀ Γ₁ Γ₂ Δ {x = x} (focr (just _) rf (unfoc ok f) eq refl ξ) = ⊥-elim (∙l⇑-at x f)

only-lf⇑-at-rf⇑N : ∀ {S} Γ₀ Γ₁ Γ₂ Δ {X Q R}
  {s : isIrr S} {x : isAt X} {n : isNeg (Δ ⊸⋆ R)} {q : isPosAt Q}
  {lf : at→posat x ⇛lf S ∣ Γ₀}
  {rf : just (Δ ⊸⋆ R , neg→negat n) MMF.⇛rf Γ₂ ； Q}
  (f : (∘ , just X) MMF.∣ ∘cxt Γ₁ ++ ∘cxt Δ ⇑ (∘ , R)) → 
  only-lf⇑-at (∘cxt (Γ₁ ++ Γ₂)) s x lf (only-rf⇑N (∘cxt Γ₁) Δ n q rf f)   
    ≡ foc s q (focl {Γ₀ = ∘cxt Γ₀} (at→posat x) lf (focr {Γ₀ = ∘cxt Γ₁} {Γ₁ = ∘cxt Γ₂} (just (Δ ⊸⋆ R , neg→negat n)) rf (unfoc (inj₂ (x , n)) (MMF.⊸r⋆⇑ Δ f)) refl refl tt) refl refl tt)
only-lf⇑-at-rf⇑N Γ₀ Γ₁ Γ₂ Δ (⊸r f) =
  trans (only-lf⇑-at-rf⇑N Γ₀ Γ₁ Γ₂ (Δ ∷ʳ _) f)
        (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (⊸r⋆⊸r⋆⇑ Δ (_ ∷ []) _)))))
only-lf⇑-at-rf⇑N Γ₀ Γ₁ Γ₂ Δ {` X} {s = s} {q = q} (foc _ r f) =
  congfoc (only-lf-f-rf-fN Γ₀ Γ₁ Γ₂ Δ {s = s}{q = q} f)

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

only-lf⇑-rf⇑ Γ₀ Γ₁ Γ₂ {` x} {R = I} (inj₁ p) f = only-lf⇑P-rf⇑-at Γ₀ Γ₁ Γ₂ f done
only-lf⇑-rf⇑ Γ₀ Γ₁ Γ₂ {` x} {R = R ⊗ R₁} (inj₁ p) f = only-lf⇑P-rf⇑-at Γ₀ Γ₁ Γ₂ f done
only-lf⇑-rf⇑ Γ₀ Γ₁ Γ₂ {M ⊸ M₁} {R = I} (inj₁ p) f = only-lf⇑P-rf⇑N [] Γ₀ Γ₁ Γ₂ [] f done
only-lf⇑-rf⇑ Γ₀ Γ₁ Γ₂ {M ⊸ M₁} {R = R ⊗ R₁} (inj₁ p) f = only-lf⇑P-rf⇑N [] Γ₀ Γ₁ Γ₂ [] f done
only-lf⇑-rf⇑ Γ₀ Γ₁ Γ₂ {M ⊸ M₁} {R = ` X} (inj₂ (x , n)) f = only-lf⇑-at-rf⇑N Γ₀ Γ₁ Γ₂ [] f

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
  rewrite ++?-alt-eq₁ (∘cxt Λ) (∘cxt Γ₁) (∘cxt Γ₂) | ++?-eq₁ (∘cxt Λ) [] (∘cxt Γ₁) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (only-lf⇑-⊸r⋆⇑ (∘cxt Γ₁) Δ {lf = lf} _))
                    (trans (sym (⊸r⋆runL Δ ℓ))
                           (cong (MMF.⊸r⋆⇑ Δ) (runLeq ℓ))))))
only-lf-fP-rf-fN {S} _ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = .(map (λ z → ∘ , z) Λ)} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (_ , refl , refl) | inj₁ (Λ , A ∷ Λ' , refl , refl , refl) 
  rewrite ++?-alt-eq₁ (∘cxt (Λ ++ A ∷ Λ')) (∘cxt Γ₁) (∘cxt Γ₂) | ++?-alt-eq₂ (∘fma A) (∘cxt Λ) (∘cxt Λ') (∘cxt Γ₁) | split-map-eq ∘fma Λ (A ∷ Λ') =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (only-lf⇑-⊸r⋆⇑ (∘cxt (_ ∷ Λ') ++ ∘cxt Γ₁) Δ {lf = lf} _))
                    (trans (sym (⊸r⋆runL Δ ℓ))
                           (cong (MMF.⊸r⋆⇑ Δ) (runLeq ℓ))))))
only-lf-fP-rf-fN {S} Γ Γ₀ .(A ∷ Λ ++ Λ') Γ₂ Δ (focl {Γ₀ = .(map (λ z → ∘ , z) Γ ++ (∘ , A) ∷ map (λ z → ∘ , z) Λ)} {.(map (λ z → ∘ , z) Λ' ++ map _ Δ)} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Λ') , refl , refl) | inj₂ (A , Λ , Λ' , refl , refl , refl)
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt (A ∷ Λ ++ Λ')) (∘cxt Γ₂) | ++?-eq₂ (∘fma A) (∘cxt Γ) (∘cxt Λ) (∘cxt Λ') =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (_ ∷ Λ ++ Λ')} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (only-lf⇑-⊸r⋆⇑ (∘cxt Λ') Δ {lf = lf} _))
                    (trans (sym (⊸r⋆runL Δ ℓ))
                           (cong (MMF.⊸r⋆⇑ Δ) (runLeq ℓ))))))

only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₅} q lf (focr {Γ₀ = Γ₃}{Γ₄} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ with ++? (∘cxt (Γ ++ Γ₁)) Γ₅ (∘cxt Δ) (Γ₃ ++ Γ₄) eq
... | inj₂ (A , Ω , refl , eq') with split-map ∘fma Δ (A ∷ Ω) (Γ₃ ++ Γ₄) eq'
... | A' ∷ Ξ , Ξ' , refl , eq₀ , refl with split-map ∘fma Ξ' Γ₃ Γ₄ eq₀
only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ .((A' ∷ Ξ) ++ Γ₃' ++ Γ₄') (focl {_} {_} {_} {_} {.(map _ Γ ++ map _ Γ₁ ++ (∘ , A') ∷ map _ Ξ)} q lf (focr {Γ₀ = .(map (λ A → ∘ , A) Γ₃')} {.(map (λ A → ∘ , A) Γ₄')} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₂ (.(∘ , A') , .(map _ Ξ) , refl , eq') | A' ∷ Ξ , .(Γ₃' ++ Γ₄') , refl , eq₀ , refl | Γ₃' , Γ₄' , refl , refl , refl
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt Γ₁) (∘cxt Γ₂) =
  congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} (inj₁ _))
           (trans (cong (MMF.runL ℓ) (l∙→∘⇑⊸r⋆ {Γ = ∘cxt (Γ ++ Γ₁)} (_ ∷ Ξ ++ Γ₃' ++ Γ₄') _))
                  (trans (sym (⊸r⋆runL (_ ∷ Ξ ++ Γ₃' ++ Γ₄') ℓ))
                         (cong (MMF.⊸r⋆⇑ (_ ∷ Ξ ++ Γ₃' ++ Γ₄')) (runLeq ℓ))))))
only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₅} q lf (focr {Γ₀ = Γ₃} {Γ₄} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ | inj₁ (Ω , eq' , eq'') with ++? Ω Γ₃ (∘cxt Δ) Γ₄ eq'
... | inj₂ (A , Ω , refl , eq₁) with split-map ∘fma Δ (A ∷ Ω) Γ₄ eq₁
only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ .((A' ∷ Ω') ++ Γ₄') (focl {Γ₀ = Γ₅} q lf (focr {_} {_} {_} {_} {_} {.(Ω ++ (∘ , A') ∷ map (λ A → ∘ , A) Ω')} {.(map (λ A → ∘ , A) Γ₄')} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ | inj₁ (Ω , refl , eq'') | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Ω') , refl , eq₁) | A' ∷ Ω' , Γ₄' , refl , refl , refl with split-map++ Γ₅ Ω Γ Γ₁ (sym eq'')
only-lf-fP-rf-fN ._ Γ₀ Γ₁ Γ₂ .((A' ∷ Ω') ++ Γ₄') (focl {Γ₀ = .(map (λ z → ∘ , z) Ξ)} q lf (focr {_} {_} {_} {_} {_} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (_ , refl , refl) | inj₂ (.(∘ , A') , .(map _ Ω') , refl , eq₁) | A' ∷ Ω' , Γ₄' , refl , refl , refl | inj₁ (Ξ , [] , refl , refl , refl)
  rewrite ++?-eq₂ (∘fma A') (∘cxt Γ₁) (∘cxt Ω') (∘cxt Γ₄') | split-map-eq ∘fma Ω' Γ₄' | ++?-alt-eq₁ (∘cxt Ξ) (∘cxt Γ₁) (∘cxt Γ₂) | ++?-eq₁ (∘cxt Ξ) [] (∘cxt Γ₁) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (only-lf⇑-⊸r⋆⇑ (∘cxt Γ₁) (_ ∷ Ω' ++ Γ₄') {lf = lf}_))
                    (trans (sym (⊸r⋆runL (_ ∷ Ω' ++ Γ₄') ℓ))
                           (cong (MMF.⊸r⋆⇑ (_ ∷ Ω' ++ Γ₄')) (trans (runLeq ℓ)
                                                                    (cong (MMF.runLQ _ ℓ) (only-lf⇑-rf⇑ Ξ (Γ₁ ++ A' ∷ Ω') Γ₄' ok f ))) )))))
only-lf-fP-rf-fN ._ Γ₀ Γ₁ Γ₂ .((A' ∷ Ω') ++ Γ₄') (focl {Γ₀ = .(map (λ z → ∘ , z) Ξ)} q lf (focr {_} {_} {_} {_} {_} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (_ , refl , refl) | inj₂ (.(∘ , A') , .(map _ Ω') , refl , eq₁) | A' ∷ Ω' , Γ₄' , refl , refl , refl | inj₁ (Ξ , A'' ∷ Ξ' , refl , refl , refl)
  rewrite ++?-eq₂ (∘fma A') (∘cxt (A'' ∷ Ξ' ++ Γ₁)) (∘cxt Ω') (∘cxt Γ₄') | split-map-eq ∘fma Ω' Γ₄' | ++?-alt-eq₁ (∘cxt (Ξ ++ A'' ∷ Ξ')) (∘cxt Γ₁) (∘cxt Γ₂) | ++?-eq₁ (∘cxt Ξ) (∘cxt (A'' ∷ Ξ')) (∘cxt Γ₁) | split-map-eq ∘fma Ξ (A'' ∷ Ξ') =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (only-lf⇑-⊸r⋆⇑ (∘cxt (A'' ∷ Ξ' ++ Γ₁)) (_ ∷ Ω' ++ Γ₄') {lf = lf}_))
                    (trans (sym (⊸r⋆runL (_ ∷ Ω' ++ Γ₄') ℓ))
                           (cong (MMF.⊸r⋆⇑ (_ ∷ Ω' ++ Γ₄')) (trans (runLeq ℓ)
                                                                    (cong (MMF.runLQ _ ℓ) (only-lf⇑-rf⇑ Ξ (A'' ∷ Ξ' ++ Γ₁ ++ A' ∷ Ω') Γ₄' ok f))))))))
only-lf-fP-rf-fN Γ Γ₀ .(A'' ∷ Ξ ++ Ξ') Γ₂ .((A' ∷ Ω') ++ Γ₄') (focl {Γ₀ = .(map (λ z → ∘ , z) Γ ++ (∘ , A'') ∷ map (λ z → ∘ , z) Ξ)} q lf (focr {_} {_} {_} {_} {_} {.(map (λ z → ∘ , z) Ξ' ++ (∘ , A') ∷ map _ Ω')} {.(map _ Γ₄')} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Ξ') , refl , refl) | inj₂ (.(∘ , A') , .(map _ Ω') , refl , eq₁) | A' ∷ Ω' , Γ₄' , refl , refl , refl | inj₂ (A'' , Ξ , Ξ' , refl , refl , refl)
  rewrite ++?-eq₂ (∘fma A') (∘cxt Ξ') (∘cxt Ω') (∘cxt Γ₄') | split-map-eq ∘fma Ω' Γ₄' | ++?-alt-eq₁ (∘cxt Γ) (∘cxt (A'' ∷ Ξ ++ Ξ')) (∘cxt Γ₂) | ++?-alt-eq₁ (∘cxt Γ) (∘cxt (A'' ∷ Ξ)) (∘cxt Ξ') =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (_ ∷ Ξ ++ Ξ')} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (only-lf⇑-⊸r⋆⇑ (∘cxt Ξ') (_ ∷ Ω' ++ Γ₄') {lf = lf}_))
                    (trans (sym (⊸r⋆runL (_ ∷ Ω' ++ Γ₄') ℓ))
                           (cong (MMF.⊸r⋆⇑ (_ ∷ Ω' ++ Γ₄')) (trans (runLeq ℓ)
                                                                   (cong (MMF.runLQ _ ℓ) (only-lf⇑-rf⇑ (Γ ++ A'' ∷ Ξ) (Ξ' ++ A' ∷ Ω') Γ₄' ok f))))))))
only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₅} q lf (focr {Γ₀ = Γ₃} {.(Ω ++ map (λ A → ∘ , A) Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ | inj₁ (.(Γ₃ ++ Ω) , refl , eq'') | inj₁ (Ω , refl , refl) with split-map++ Γ₅ (Γ₃ ++ Ω) Γ Γ₁ (sym eq'')
... | inj₂ (A , Ξ , Ξ' , refl , refl , eq₂) with split-map ∘fma Ξ' Γ₃ Ω (sym eq₂)
only-lf-fP-rf-fN Γ Γ₀ .(A ∷ Ξ ++ Γ₃' ++ Ω') Γ₂ Δ (focl {_} {_} {_} {_} {.(map _ Γ ++ (∘ , A) ∷ map _ Ξ)} q lf (focr {Γ₀ = .(map (λ A₁ → ∘ , A₁) Γ₃')} {.(map (λ A₁ → ∘ , A₁) Ω' ++ map _ Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ A₁ → ∘ , A₁) Γ₃' ++ map (λ A₁ → ∘ , A₁) Ω') , refl , refl) | inj₁ (.(map (λ A₁ → ∘ , A₁) Ω') , refl , refl) | inj₂ (A , Ξ , .(Γ₃' ++ Ω') , refl , refl , eq₂) | Γ₃' , Ω' , refl , refl , refl
  rewrite ++?-eq₁ (∘cxt Γ₃') (∘cxt Ω') (∘cxt Δ) | ++?-alt-eq₁ (∘cxt Γ) (∘cxt (A ∷ Ξ ++ Γ₃' ++ Ω')) (∘cxt Γ₂) | ++?-alt-eq₁ (∘cxt Γ) (∘cxt (A ∷ Ξ)) (∘cxt (Γ₃' ++ Ω')) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (_ ∷ Ξ ++ Γ₃' ++ Ω')} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (only-lf⇑-⊸r⋆⇑ (∘cxt (Γ₃' ++ Ω')) Δ {lf = lf}_))
                    (trans (sym (⊸r⋆runL Δ ℓ))
                           (cong (MMF.⊸r⋆⇑ Δ) (trans (runLeq ℓ)
                                                     (cong (MMF.runLQ _ ℓ) (only-lf⇑-rf⇑ (Γ ++ A ∷ Ξ) Γ₃' (Ω' ++ Δ) ok f))))))))
only-lf-fP-rf-fN {S} .(Ξ ++ Ξ') Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = .(map (λ z → ∘ , z) Ξ)} q lf (focr {Γ₀ = Γ₃} {.(Ω ++ map _ Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ | inj₁ (.(Γ₃ ++ Ω) , refl , eq'') | inj₁ (Ω , refl , refl) | inj₁ (Ξ , Ξ' , eq₀ , refl , refl) with split-map++ Γ₃ Ω Ξ' Γ₁ eq₀
only-lf-fP-rf-fN {S} _ Γ₀ Γ₁ Γ₂ Δ (focl {_} {_} {_} {_} {.(map _ Ξ)} q lf (focr (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (_ , refl , refl) | inj₁ (_ , refl , refl) | inj₁ (Ξ , _ , eq₀ , refl , refl) | inj₁ ([] , [] , refl , refl , refl)
  rewrite ++?-eq₁ [] (∘cxt Γ₁) (∘cxt Δ) | ++?-alt-eq₁ (∘cxt Ξ) (∘cxt Γ₁) (∘cxt Γ₂) | ++?-alt-eq₁ (∘cxt Ξ) [] (∘cxt Γ₁) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (only-lf⇑-⊸r⋆⇑ (∘cxt Γ₁) Δ {lf = lf}_))
                    (trans (sym (⊸r⋆runL Δ ℓ))
                           (cong (MMF.⊸r⋆⇑ Δ) (trans (runLeq ℓ)
                                                     (cong (MMF.runLQ _ ℓ) (only-lf⇑-rf⇑ Ξ [] (Γ₁ ++ Δ) ok f))))))))
only-lf-fP-rf-fN {S} _ Γ₀ Γ₁ Γ₂ Δ (focl {_} {_} {_} {_} {.(map _ Ξ)} q lf (focr (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (_ , refl , refl) | inj₁ (_ , refl , refl) | inj₁ (Ξ , _ , eq₀ , refl , refl) | inj₁ (A ∷ Ξ'' , [] , refl , refl , refl)
  rewrite ++?-eq₁ (∘cxt (A ∷ Ξ'')) (∘cxt Γ₁) (∘cxt Δ) | ++?-alt-eq₁ (∘cxt (Ξ ++ A ∷ Ξ'')) (∘cxt Γ₁) (∘cxt Γ₂) | ++?-alt-eq₂ (∘fma A) (∘cxt Ξ) (∘cxt Ξ'') (∘cxt Γ₁) | split-map-eq ∘fma Ξ (A ∷ Ξ'') = 
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (only-lf⇑-⊸r⋆⇑ (∘cxt (A ∷ Ξ'' ++ Γ₁)) Δ {lf = lf}_))
                    (trans (sym (⊸r⋆runL Δ ℓ))
                           (cong (MMF.⊸r⋆⇑ Δ) (trans (runLeq ℓ)
                                                     (cong (MMF.runLQ _ ℓ) (only-lf⇑-rf⇑ Ξ (A ∷ Ξ'') (Γ₁ ++ Δ) ok f))))))))
only-lf-fP-rf-fN {S} _ Γ₀ Γ₁ Γ₂ Δ (focl {_} {_} {_} {_} {.(map _ Ξ)} q lf (focr (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (_ , refl , refl) | inj₁ (_ , refl , refl) | inj₁ (Ξ , _ , eq₀ , refl , refl) | inj₁ ([] , A ∷ Ξ''' , refl , refl , refl)
  rewrite ++?-eq₁ [] (∘cxt (A ∷ Ξ''' ++ Γ₁)) (∘cxt Δ) | ++?-alt-eq₁ (∘cxt (Ξ ++ A ∷ Ξ''')) (∘cxt Γ₁) (∘cxt Γ₂) | ++?-eq₁ (∘cxt Ξ) (∘cxt (A ∷ Ξ''')) (∘cxt Γ₁) | split-map-eq ∘fma Ξ (A ∷ Ξ''') =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (only-lf⇑-⊸r⋆⇑ (∘cxt (A ∷ Ξ''' ++ Γ₁)) Δ {lf = lf}_))
                    (trans (sym (⊸r⋆runL Δ ℓ))
                           (cong (MMF.⊸r⋆⇑ Δ) (trans (runLeq ℓ)
                                                     (cong (MMF.runLQ _ ℓ) (only-lf⇑-rf⇑ Ξ [] (A ∷ Ξ''' ++ Γ₁ ++ Δ) ok f))))))))
only-lf-fP-rf-fN {S} _ Γ₀ Γ₁ Γ₂ Δ (focl {_} {_} {_} {_} {.(map _ Ξ)} q lf (focr (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (_ , refl , refl) | inj₁ (_ , refl , refl) | inj₁ (Ξ , _ , eq₀ , refl , refl) | inj₁ (A' ∷ Ξ'' , A ∷ Ξ''' , refl , refl , refl)
  rewrite ++?-eq₁ (∘cxt (A' ∷ Ξ'')) (∘cxt (A ∷ Ξ''' ++ Γ₁)) (∘cxt Δ) | ++?-alt-eq₁ (∘cxt (Ξ ++ A' ∷ Ξ'' ++ A ∷ Ξ''')) (∘cxt Γ₁) (∘cxt Γ₂) | ++?-eq₁ (∘cxt Ξ) (∘cxt (A' ∷ Ξ'' ++ A ∷ Ξ''')) (∘cxt Γ₁) | split-map-eq ∘fma Ξ (A' ∷ Ξ'' ++ A ∷ Ξ''') =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (only-lf⇑-⊸r⋆⇑ (∘cxt (A' ∷ Ξ'' ++ A ∷ Ξ''' ++ Γ₁)) Δ {lf = lf}_))
                    (trans (sym (⊸r⋆runL Δ ℓ))
                           (cong (MMF.⊸r⋆⇑ Δ) (trans (runLeq ℓ)
                                                     (cong (MMF.runLQ _ ℓ) (only-lf⇑-rf⇑ Ξ (A' ∷ Ξ'') (A ∷ Ξ''' ++ Γ₁ ++ Δ) ok f))))))))
only-lf-fP-rf-fN _ Γ₀ .(A ∷ Ξ'' ++ Ξ''') Γ₂ Δ (focl {_} {_} {_} {_} {.(map _ Ξ)} q lf (focr (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (_ , refl , refl) | inj₁ (.(map (λ z → ∘ , z) Ξ''') , refl , refl) | inj₁ (Ξ , [] , eq₀ , refl , refl) | inj₂ (A , Ξ'' , Ξ''' , refl , refl , refl)
  rewrite ++?-eq₁ (∘cxt (A ∷ Ξ'')) (∘cxt Ξ''') (∘cxt Δ) | ++?-alt-eq₁ (∘cxt Ξ) (∘cxt (A ∷ Ξ'' ++ Ξ''')) (∘cxt Γ₂) | ++?-alt-eq₁ (∘cxt Ξ) [] (∘cxt (A ∷ Ξ'' ++ Ξ''')) =
        congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (A ∷ Ξ'' ++ Ξ''')} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (only-lf⇑-⊸r⋆⇑ (∘cxt (A ∷ Ξ'' ++ Ξ''')) Δ {lf = lf}_))
                    (trans (sym (⊸r⋆runL Δ ℓ))
                           (cong (MMF.⊸r⋆⇑ Δ) (trans (runLeq ℓ)
                                                     (cong (MMF.runLQ _ ℓ) (only-lf⇑-rf⇑ Ξ (A ∷ Ξ'') (Ξ''' ++ Δ) ok f))))))))
only-lf-fP-rf-fN _ Γ₀ .(A ∷ Ξ'' ++ Ξ''') Γ₂ Δ (focl {_} {_} {_} {_} {.(map _ Ξ)} q lf (focr (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (_ , refl , refl) | inj₁ (.(map (λ z → ∘ , z) Ξ''') , refl , refl) | inj₁ (Ξ , A' ∷ Ξ' , eq₀ , refl , refl) | inj₂ (A , Ξ'' , Ξ''' , refl , refl , refl)
  rewrite ++?-eq₁ (∘cxt (A' ∷ Ξ' ++ A ∷ Ξ'')) (∘cxt Ξ''') (∘cxt Δ) | ++?-alt-eq₁ (∘cxt (Ξ ++ A' ∷ Ξ')) (∘cxt (A ∷ Ξ'' ++ Ξ''')) (∘cxt Γ₂) | ++?-alt-eq₂ (∘fma A') (∘cxt Ξ) (∘cxt Ξ') (∘cxt (A ∷ Ξ'' ++ Ξ''')) | split-map-eq ∘fma Ξ (A' ∷ Ξ') =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (A ∷ Ξ'' ++ Ξ''')} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (only-lf⇑-⊸r⋆⇑ (∘cxt (A' ∷ Ξ' ++ A ∷ Ξ'' ++ Ξ''')) Δ {lf = lf}_))
                    (trans (sym (⊸r⋆runL Δ ℓ))
                           (cong (MMF.⊸r⋆⇑ Δ) (trans (runLeq ℓ)
                                                     (cong (MMF.runLQ _ ℓ) (only-lf⇑-rf⇑ Ξ (A' ∷ Ξ' ++ A ∷ Ξ'') (Ξ''' ++ Δ) ok f))))))))

only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₃}{Γ₄} q lf (unfoc ok f) refl refl ξ) eq ℓ with ++? (∘cxt (Γ ++ Γ₁)) Γ₃ (∘cxt Δ) Γ₄ eq
... | inj₂ (A , Λ , refl , eq') with split-map ∘fma Δ (A ∷ Λ) Γ₄ eq'
only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ .((A' ∷ Λ') ++ Γ₄') (focl {_} {_} {_} {_} {.(map _ Γ ++ map _ Γ₁ ++ (∘ , A') ∷ map (λ A → ∘ , A) Λ')} {.(map (λ A → ∘ , A) Γ₄')} q lf (unfoc ok f) refl refl ξ) refl ℓ | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Λ') , refl , eq') | A' ∷ Λ' , Γ₄' , refl , refl , refl 
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt Γ₁) (∘cxt Γ₂) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (l∙→∘⇑⊸r⋆ {Γ = ∘cxt (Γ ++ Γ₁)} (_ ∷ Λ' ++ Γ₄') _))
               (trans (sym (⊸r⋆runL (_ ∷ Λ' ++ Γ₄') ℓ))
                      (cong (MMF.⊸r⋆⇑ (_ ∷ Λ' ++ Γ₄')) (runLeq ℓ))))))
only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₃} {.(Λ ++ map (λ A → ∘ , A) Δ)} q lf (unfoc ok f) refl refl ξ) eq ℓ | inj₁ (Λ , refl , eq') with split-map++ Γ₃ Λ Γ Γ₁ (sym eq')
only-lf-fP-rf-fN _ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = .(map (λ z → ∘ , z) Ω)} q lf (unfoc ok f) refl refl ξ) refl ℓ | inj₁ (_ , refl , refl) | inj₁ (Ω , [] , refl , refl , refl)
  rewrite ++?-alt-eq₁ (∘cxt Ω) (∘cxt Γ₁) (∘cxt Γ₂) | ++?-alt-eq₁ (∘cxt Ω) [] (∘cxt Γ₁) | isProp-isPosAt q (pos→posat ok) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (only-lf⇑-⊸r⋆⇑ (∘cxt Γ₁) Δ {lf = lf} _))
                    (trans (sym (⊸r⋆runL Δ ℓ))
                           (cong (MMF.⊸r⋆⇑ Δ) (trans (runLeq ℓ)
                                                     (cong (MMF.runLQ _ ℓ) (trans (only-lf⇑≡ {lf = lf} _)
                                                                                  (only-lf⇑P-r∙ {Δ₁ = Γ₁ ++ Δ} _ done)))))))))
only-lf-fP-rf-fN _ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = .(map (λ z → ∘ , z) Ω)} q lf (unfoc ok f) refl refl ξ) refl ℓ | inj₁ (_ , refl , refl) | inj₁ (Ω , A ∷ Ω' , refl , refl , refl)
  rewrite ++?-alt-eq₁ (∘cxt (Ω ++ A ∷ Ω')) (∘cxt Γ₁) (∘cxt Γ₂) | ++?-alt-eq₂ (∘fma A) (∘cxt Ω) (∘cxt Ω') (∘cxt Γ₁) | split-map-eq ∘fma Ω (A ∷ Ω') | isProp-isPosAt q (pos→posat ok) = 
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (only-lf⇑-⊸r⋆⇑ (∘cxt (A ∷ Ω' ++ Γ₁)) Δ {lf = lf} _))
                    (trans (sym (⊸r⋆runL Δ ℓ))
                           (cong (MMF.⊸r⋆⇑ Δ) (trans (runLeq ℓ)
                                                     (cong (MMF.runLQ _ ℓ) (trans (only-lf⇑≡ {lf = lf} _)
                                                                                  (only-lf⇑P-r∙ {Δ₁ = A ∷ Ω' ++ Γ₁ ++ Δ} _ done)))))))))
only-lf-fP-rf-fN Γ Γ₀ .(A ∷ Ω ++ Ω') Γ₂ Δ (focl {Γ₀ = .(map (λ z → ∘ , z) Γ ++ (∘ , A) ∷ map (λ z → ∘ , z) Ω)} {.(map (λ z → ∘ , z) Ω' ++ map _ Δ)} q lf (unfoc ok f) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Ω') , refl , refl) | inj₂ (A , Ω , Ω' , refl , refl , refl)
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt (A ∷ Ω ++ Ω')) (∘cxt Γ₂) | ++?-alt-eq₁ (∘cxt Γ) (∘cxt (A ∷ Ω)) (∘cxt Ω') | isProp-isPosAt q (pos→posat ok) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (A ∷ Ω ++ Ω')} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (only-lf⇑-⊸r⋆⇑ (∘cxt Ω') Δ {lf = lf} _))
                    (trans (sym (⊸r⋆runL Δ ℓ))
                           (cong (MMF.⊸r⋆⇑ Δ) (trans (runLeq ℓ)
                                                     (cong (MMF.runLQ _ ℓ) (trans (only-lf⇑≡ {lf = lf} _)
                                                                                  (only-lf⇑P-r∙ {Δ₁ = Ω' ++ Δ} _ done)))))))))

only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focr {Γ₀ = Γ₃} {Γ₄} (just (M , m)) rf (unfoc ok f) refl refl ξ) eq ℓ with ++? (∘cxt (Γ ++ Γ₁)) Γ₃ (∘cxt Δ) Γ₄ eq
... | inj₂ (A , Λ , refl , eq') with split-map ∘fma Δ (A ∷ Λ) Γ₄ eq'
only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ .((A' ∷ Λ') ++ Γ₄') (focr {_} {_} {_} {_} {_} {.(map _ Γ ++ map _ Γ₁ ++ (∘ , A') ∷ map (λ A → ∘ , A) Λ')} {.(map (λ A → ∘ , A) Γ₄')} (just (M , m)) rf (unfoc ok f) refl refl ξ) refl ℓ | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Λ') , refl , eq') | A' ∷ Λ' , Γ₄' , refl , refl , refl 
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt Γ₁) (∘cxt Γ₂) =
        congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} (inj₁ _))
                 (trans (cong (MMF.runL ℓ) (l∙→∘⇑⊸r⋆ {Γ = ∘cxt (Γ ++ Γ₁)} (_ ∷ Λ' ++ Γ₄') _))
                        (trans (sym (⊸r⋆runL (_ ∷ Λ' ++ Γ₄') ℓ))
                               (cong (MMF.⊸r⋆⇑ (_ ∷ Λ' ++ Γ₄')) (runLeq ℓ))))))
only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focr {Γ₀ = Γ₃} {.(Λ ++ map (λ A → ∘ , A) Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ) eq ℓ | inj₁ (Λ , refl , eq') with split-map++ Γ₃ Λ Γ Γ₁ (sym eq')
only-lf-fP-rf-fN .(Ω ++ Ω') Γ₀ Γ₁ Γ₂ Δ (focr {Γ₀ = .(map (λ z → ∘ , z) Ω)} {.((map (λ z → ∘ , z) Ω' ++ map (λ z → ∘ , z) Γ₁) ++ map _ Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Ω' ++ map (λ z → ∘ , z) Γ₁) , refl , refl) | inj₁ (Ω , Ω' , refl , refl , refl)
  rewrite ++?-alt-eq₁ (∘cxt (Ω ++ Ω')) (∘cxt Γ₁) (∘cxt Γ₂) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (l∙→∘⇑⊸r⋆ {Γ = ∘cxt (Ω ++ Ω' ++ Γ₁)} Δ _))
                    (trans (sym (⊸r⋆runL Δ ℓ))
                           (cong (MMF.⊸r⋆⇑ Δ) (runLeq ℓ))))))
only-lf-fP-rf-fN Γ Γ₀ .(A ∷ Ω ++ Ω') Γ₂ Δ (focr {Γ₀ = .(map (λ z → ∘ , z) Γ ++ (∘ , A) ∷ map (λ z → ∘ , z) Ω)} {.(map (λ z → ∘ , z) Ω' ++ map _ Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Ω') , refl , refl) | inj₂ (A , Ω , Ω' , refl , refl , refl)
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt (A ∷ Ω ++ Ω')) (∘cxt Γ₂) = 
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (_ ∷ Ω ++ Ω')} (inj₁ _))
             (trans (cong (MMF.runL ℓ) (l∙→∘⇑⊸r⋆ {Γ = ∘cxt (Γ ++ _ ∷ Ω ++ Ω')} Δ _))
                    (trans (sym (⊸r⋆runL Δ ℓ))
                           (cong (MMF.⊸r⋆⇑ Δ) (runLeq ℓ))))))

only-lf-fP-rf-fN Γ Γ₀ Γ₁ Γ₂ Δ (focr ─ rf (refl , refl) refl refl ξ) refl ℓ 
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt Γ₁) (∘cxt Γ₂) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _)
             (trans (cong (MMF.runL ℓ) (l∙→∘⇑⊸r⋆ {Γ = ∘cxt (Γ ++ Γ₁)} Δ _))
                    (trans (sym (⊸r⋆runL Δ ℓ))
                           (cong (MMF.⊸r⋆⇑ Δ) (runLeq ℓ))))))


