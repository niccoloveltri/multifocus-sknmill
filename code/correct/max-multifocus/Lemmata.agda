{-# OPTIONS --rewriting #-}

module correct.max-multifocus.Lemmata where

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

cong-only-lf⇑ : {S : Stp} {Δ₀ : Cxt} {Δ₁ : TCxt} {C Q : Fma}
               {s : isIrr S} {q : isPosAt Q}
               {lf lf' : q ⇛lf S ∣ Δ₀} (eq : lf ≡ lf')
               {f g : (∘ , just Q) MMF.∣ Δ₁ ⇑ (∘ , C)} (eq' : f ≡ g)
               → only-lf⇑ Δ₁ s q lf f ≡ only-lf⇑ Δ₁ s q lf' g
cong-only-lf⇑ refl refl = refl

cong-only-rf⇑ : {S : Stp} {Δ₀ : TCxt} {Δ₁ : Cxt} {M Q : Fma}
              {m : isNegAt M} {q : isPosAt Q}
              {rf rf' : just (M , m) MMF.⇛rf Δ₁ ； Q} (eq : rf ≡ rf')
              {f g : (∘ , S) MMF.∣ Δ₀ ⇑ (∘ , M)} (eq' : f ≡ g) → 
              ------------------------------------
               only-rf⇑ Δ₀ m q rf f ≡ only-rf⇑ Δ₀ m q rf' g
cong-only-rf⇑ refl refl = refl               

Il⇑eq : ∀ {b Γ Q} {q : isPosAt Q}
        (f :  (∘ , ─) MMF.∣ Γ ⇑ (b , Q)) →
  -------------------------
       MMF.Il⇑ f ≡ Il q f
Il⇑eq {Q = ` x} (foc s q f) = refl
Il⇑eq {Q = I} (foc s q f) = refl
Il⇑eq {Q = Q ⊗ Q₁} (foc s q f) = refl

⊗l⇑eq : ∀ {b Γ A B Q} {q : isPosAt Q}
        (f :  (∘ , just A) MMF.∣ (b , B) ∷ Γ ⇑ (b , Q)) →
  -------------------------
       MMF.⊗l⇑ f ≡ ⊗l q f
⊗l⇑eq (Il q f) = cong (λ x → ⊗l x (Il q f)) (isProp-isPosAt _ _)
⊗l⇑eq (⊗l q f) =
  trans (cong (λ x → ⊗l x (MMF.⊗l⇑ f)) (isProp-isPosAt _ _))
        (cong (⊗l _) (⊗l⇑eq f))
⊗l⇑eq (foc s q f) = cong (λ x → ⊗l x (foc s q f)) (isProp-isPosAt _ _)

runLeq : ∀ {b S Γ Δ A Q} {q : isPosAt Q}
        {f :  (∘ , S) MMF.∣ tag-cxt b Γ ++ Δ ⇑ (b , Q)}
        (ℓ : L S Γ A) →
  -------------------------
       MMF.runL {Δ = Δ} ℓ f ≡ MMF.runLQ q ℓ f
runLeq done = refl
runLeq (Il-1 ℓ) = trans (runLeq ℓ) (cong (MMF.runLQ _ ℓ) (Il⇑eq _))
runLeq (⊗l-1 ℓ) = trans (runLeq ℓ) (cong (MMF.runLQ _ ℓ) (⊗l⇑eq _))

-- congunfoc : {b b' l r : Tag} {S : Stp} {Γ : TCxt} {C : Fma}
--           {ok : MF.UT b b' S C}
--           {f g : (not b , S) MMF.∣ ∘tcxt Γ ⇑ (not b' , C)} → f ≡ g →
--           unfoc ok f ≡ unfoc ok g
-- congunfoc refl = refl          
          

⊸r⋆⊸r⋆⇑ : {l : Tag} {S : Stp} {Γ : TCxt} (Δ Δ' : Cxt) {A : Fma}
      (f : (l , S) MMF.∣ Γ ++ tag-cxt l (Δ ++ Δ') ⇑ (∘ , A)) →
      MMF.⊸r⋆⇑ {Γ = Γ} (Δ ++ Δ') f ≡ MMF.⊸r⋆⇑ Δ (MMF.⊸r⋆⇑ Δ' f)
⊸r⋆⊸r⋆⇑ [] Δ' f = refl
⊸r⋆⊸r⋆⇑ (A' ∷ Δ) Δ' f = cong ⊸r (⊸r⋆⊸r⋆⇑ Δ Δ' f)

untag-seq≡ : {S : Stp} {Γ Γ' : TCxt} {A : Fma}
        (f : (∘ , S) MMF.∣ Γ' ⇑ (∘ , A)) (eq : Γ' ≡ ∘tcxt Γ)  →
        untag-seq (MMF.subst⇑ f eq) ≡ MMF.subst⇑ f eq
untag-seq-f≡ : {b b' : Tag} {S : Stp} {Γ Γ' : TCxt} {A : Fma}
        (f : MMF.[ b , b' ] (∘ , S) ∣ Γ' ⇓ (∘ , A)) (eq : Γ' ≡ ∘tcxt Γ)  →
        untag-seq-f (MMF.subst⇓ f eq) ≡ MMF.subst⇓ f eq

untag-seq≡ {Γ = Γ} (⊸r f) refl = cong ⊸r (untag-seq≡ {Γ = Γ ∷ʳ (∘ , _)} f refl)
untag-seq≡ (Il q f) refl = cong (Il q) (untag-seq≡ f refl)
untag-seq≡ (⊗l q f) refl = cong (⊗l q) (untag-seq≡ {Γ = (∘ , _) ∷ _} f refl)
untag-seq≡ (foc s q f) refl = congfoc (untag-seq-f≡ f refl)

untag-seq-f≡ {Γ = Γ} (focl {Γ₀ = Γ₀} {Γ₁} q lf f eq refl ξ) refl with split-map ∘tfma Γ Γ₀ Γ₁ eq
untag-seq-f≡ (focl q lf f refl refl ξ) refl | _ , _ , refl , refl , refl =
  congfocl refl (untag-seq-f≡ f refl)
untag-seq-f≡ {Γ = Γ} (focr {Γ₀ = Γ₀} {Γ₁} s rf f eq refl ξ) refl with split-map ∘tfma Γ Γ₀ Γ₁ eq
untag-seq-f≡ (focr (just _) lf f refl refl ξ) refl | _ , _ , refl , refl , refl =
  congfocr refl (untag-seq-f≡ f refl)
untag-seq-f≡ (focr ─ lf (refl , refl) refl refl ξ) refl | [] , _ , refl , refl , refl = refl
untag-seq-f≡ (unfoc ok f) refl = refl
untag-seq-f≡ {Γ = []} ax refl = refl

∙l⇑-at : ∀ {Γ A X} (x : isAt X) → (∙ , just X) MMF.∣ Γ ⇑ (∘ , A) → ⊥
∙l⇓-at : ∀ {Γ A X} (x : isAt X) → MMF.[ ∘ , ∘ ] (∙ , just X) ∣ Γ ⇓ (∘ , A) → ⊥

∙l⇑-at x (⊸r f) = ∙l⇑-at x f
∙l⇑-at x (foc s q f) = ∙l⇓-at x f

∙l⇓-at x (focl {Γ₀ = []} q blurl f eq eq' ξ) = ξ
∙l⇓-at x (focl {Γ₀ = _ ∷ Γ₀} q blurl f eq () ξ)
∙l⇓-at x (focr (just _) rf (unfoc ok f) eq eq' ξ) = ∙l⇑-at x f

∙r⇑-at : ∀ {S Γ X} (x : isAt X) → (∘ , S) MMF.∣ Γ ⇑ (∙ , X) → ⊥
∙r⇓-at : ∀ {S Γ X} (x : isAt X) → MMF.[ ∘ , ∘ ] (∘ , S) ∣ Γ ⇓ (∙ , X) → ⊥

∙r⇑-at x (Il q f) = ∙r⇑-at x f
∙r⇑-at x (⊗l q f) = ∙r⇑-at x f
∙r⇑-at x (foc s q f) = ∙r⇓-at x f

∙r⇓-at x (focl q lf (focr (just x₁) (⊗r+ Δ₀ Ξ m rf gs) f eq₁ eq'' ξ₁) eq eq' ξ) = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))
∙r⇓-at x (focl q lf (focr {Γ₁ = []} (just .(_ , _)) blurr f eq₁ eq'' ξ) eq eq' _) = ξ
∙r⇓-at x (focl q lf (unfoc ok f) eq eq' ξ) = ∙r⇑-at x f
∙r⇓-at x (focr s (⊗r+ Δ₀ Ξ m rf gs) f eq eq' ξ) = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))
∙r⇓-at x (focr {Γ₁ = []} .(just (_ , _)) blurr f eq eq' ξ) = ξ

only-lf⇑P-at≡ : {S S' : Stp} {Δ₀ : Cxt} (Δ₁ : TCxt) {Γ : Cxt} {P X : Fma} {x : isAt X}
            (s : isIrr S) (p : isPos P)
            (lf : pos→posat p ⇛lf S ∣ Δ₀) 
            (f : (∘ , S') MMF.∣ ∘cxt Γ ++ Δ₁ ⇑ (∘ , X)) → 
            (ℓ : MF.L S' Γ P) →
      ------------------------------------
     only-lf⇑P Δ₁ s p lf f ℓ
      ≡ foc s (at→posat x) (focl {Γ₀ = ∘cxt Δ₀} (pos→posat p) lf (focr {Γ₀ = Δ₁} (just (X , at→negat x)) blurr (unfoc (inj₁ p) (MMF.runLQ (at→posat x) ℓ (untag-seq {Γ = ∘cxt Γ ++ Δ₁} f))) refl refl tt) refl refl tt)

only-lf-fP-at≡ : {S S' : Stp} {Δ₀ : Cxt} {Δ : TCxt} (Δ₁ : TCxt) {Γ : Cxt} {P X : Fma} {x : isAt X}
            (s : isIrr S') (p : isPos P)
            (lf : pos→posat p ⇛lf S ∣ Δ₀) 
            (f : MMF.[ ∘ , ∘ ] (∘ , S') ∣ Δ ⇓ (∘ , X))
            (eq : Δ ≡ ∘cxt Γ ++ Δ₁) → 
            (ℓ : MF.L S' Γ P) →
      ------------------------------------
     only-lf-fP Δ₁ s p (at→posat x) lf f eq ℓ
      ≡ focl {Γ₀ = ∘cxt Δ₀} (pos→posat p) lf (focr {Γ₀ = Δ₁} (just (X , at→negat x)) blurr (unfoc (inj₁ p) (MMF.runLQ (at→posat x) ℓ (foc s (at→posat x) (untag-seq-f {Γ = ∘cxt Γ ++ Δ₁} (subst⇓ f eq))))) refl refl tt) refl refl tt

only-lf⇑P-at≡ Δ₁ {X = ` X} s p lf (Il q f) ℓ = only-lf⇑P-at≡ Δ₁ s p lf f (Il-1 ℓ)
only-lf⇑P-at≡ Δ₁ {X = ` X} s p lf (⊗l q f) ℓ = only-lf⇑P-at≡ Δ₁ s p lf f (⊗l-1 ℓ)
only-lf⇑P-at≡ Δ₁ {X = ` X} s p lf (foc s₁ q f) ℓ = congfoc (only-lf-fP-at≡ Δ₁ s₁ p lf f refl ℓ)

only-lf-fP-at≡ Δ₁ {x = x} s p lf (focl q lf₁ (focr (just _) (⊗r+ Δ₀ Ξ m rf gs) f eq'' eq' ξ₁) refl refl ξ) eq ℓ = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))
only-lf-fP-at≡ Δ₁ {Γ} s p lf (focl {Γ₀ = .(∘cxt Γ ++ Δ₁)} {.([] ++ [])} q lf₁ (focr {Γ₁ = []} (just (.(` _) , tt)) blurr ax refl refl ξ₁) refl refl ξ) refl ℓ
  rewrite ++?-alt-eq₁ (∘cxt Γ) Δ₁ [] = refl
only-lf-fP-at≡ Δ₁ {Γ} {X = ` X} s p lf (focl {Γ₀ = Γ₀} q lf₁ (focr {Γ₀ = Γ₁} {[]} (just .(_ , _)) blurr (unfoc (inj₁ p') f) refl refl ξ₁) refl refl ξ) eq ℓ with ++? (∘cxt Γ) Γ₀ Δ₁ Γ₁ eq
only-lf-fP-at≡ _ {Γ} {_} {` X} s p lf (focl {Γ₀ = .(map (λ A₁ → ∘ , A₁) Γ ++ A ∷ Ω)} {Q = I} q lf₁ (focr {Γ₀ = Γ₁} {[]} (just .(` X , _)) blurr (unfoc (inj₁ p') f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₂ (A , Ω , refl , refl) 
  rewrite ++?-alt-eq₁ (∘cxt Γ) (A ∷ Ω ++ Γ₁) [] | ++?-eq₂ A (∘cxt Γ) Ω Γ₁ =
    congfocl refl (congfocr refl (cong (unfoc {Γ = _ ∷ Ω ++ Γ₁} _)
      (trans (runLeq ℓ)
             (cong (MMF.runLQ tt ℓ) (trans (only-lf⇑P-at≡ (∘tcxt Γ₁) s tt lf₁ f done)
                                           (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘tcxt Γ₁} _) (untag-seq≡ {Γ = ∘tcxt Γ₁}{∘tcxt Γ₁} f refl))))))))))
only-lf-fP-at≡ _ {Γ} {_} {` X} s p lf (focl {Γ₀ = .(map (λ A₁ → ∘ , A₁) Γ ++ A ∷ Ω)} {Q = _ ⊗ _} q lf₁ (focr {Γ₀ = Γ₁} {[]} (just .(` X , _)) blurr (unfoc (inj₁ p') f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₂ (A , Ω , refl , refl) 
  rewrite ++?-alt-eq₁ (∘cxt Γ) (A ∷ Ω ++ Γ₁) [] | ++?-eq₂ A (∘cxt Γ) Ω Γ₁ =
    congfocl refl (congfocr refl (cong (unfoc {Γ = _ ∷ Ω ++ Γ₁} _)
      (trans (runLeq ℓ)
             (cong (MMF.runLQ tt ℓ) (trans (only-lf⇑P-at≡ (∘tcxt Γ₁) s tt lf₁ f done)
                                           (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘tcxt Γ₁} _) (untag-seq≡ {Γ = ∘tcxt Γ₁}{∘tcxt Γ₁} f refl))))))))))
... | inj₁ (Ω , refl , eq') with split-map ∘fma Γ Γ₀ Ω eq'
only-lf-fP-at≡ Δ₁ {.Γ₀} {_} {` X} s p lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₀)} {Q = I} q lf₁ (focr {_} {_} {_} {_} {_} {_} {[]} (just .(` X , _)) blurr (unfoc (inj₁ p') f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (._ , refl , eq') | Γ₀ , [] , refl , refl , refl
  rewrite ++?-alt-eq₁ (∘cxt Γ₀) Δ₁ [] | ++?-eq₁ (∘cxt Γ₀) [] Δ₁ =
    congfocl refl (congfocr refl (cong (unfoc {Γ = Δ₁} _)
      (trans (runLeq ℓ)
             (cong (MMF.runLQ tt ℓ) (trans (only-lf⇑P-at≡ (∘tcxt Δ₁) s _ lf₁ f done)
                                           (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘tcxt Δ₁} _) (untag-seq≡ {Γ = ∘tcxt Δ₁}{∘tcxt Δ₁} f refl)))))))) ))
only-lf-fP-at≡ Δ₁ {.Γ₀} {_} {` X} s p lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₀)} {Q = _ ⊗ _} q lf₁ (focr {_} {_} {_} {_} {_} {_} {[]} (just .(` X , _)) blurr (unfoc (inj₁ p') f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (._ , refl , eq') | Γ₀ , [] , refl , refl , refl
  rewrite ++?-alt-eq₁ (∘cxt Γ₀) Δ₁ [] | ++?-eq₁ (∘cxt Γ₀) [] Δ₁ =
    congfocl refl (congfocr refl (cong (unfoc {Γ = Δ₁} _)
      (trans (runLeq ℓ)
             (cong (MMF.runLQ tt ℓ) (trans (only-lf⇑P-at≡ (∘tcxt Δ₁) s _ lf₁ f done)
                                           (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘tcxt Δ₁} _) (untag-seq≡ {Γ = ∘tcxt Δ₁}{∘tcxt Δ₁} f refl)))))))) ))
only-lf-fP-at≡ Δ₁ {_} {_} {` X} s p lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₀)} {Q = I} q lf₁ (focr {_} {_} {_} {_} {_} {_} {[]} (just .(` X , _)) blurr (unfoc (inj₁ p') f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (._ , refl , eq') | Γ₀ , A ∷ Ω , refl , refl , refl
  rewrite ++?-alt-eq₁ (∘cxt (Γ₀ ++ A ∷ Ω)) Δ₁ [] | ++?-alt-eq₂ (∘fma A) (∘cxt Γ₀) (∘cxt Ω) Δ₁ | split-map-eq ∘fma Γ₀ (A ∷ Ω) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = Δ₁} _)
      (trans (runLeq ℓ)
             (cong (MMF.runLQ tt ℓ) (trans (only-lf⇑P-at≡ (_ ∷ ∘cxt Ω ++ ∘tcxt Δ₁) s _ lf₁ f done)
                                           (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = _ ∷ ∘cxt Ω ++ ∘tcxt Δ₁} _) (untag-seq≡ {Γ = ∘cxt (_ ∷ Ω) ++ ∘tcxt Δ₁}{_ ∷ ∘cxt Ω ++ ∘tcxt Δ₁} _ refl))))))))))
only-lf-fP-at≡ Δ₁ {_} {_} {` X} s p lf (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₀)} {Q = _ ⊗ _} q lf₁ (focr {_} {_} {_} {_} {_} {_} {[]} (just .(` X , _)) blurr (unfoc (inj₁ p') f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (._ , refl , eq') | Γ₀ , A ∷ Ω , refl , refl , refl
  rewrite ++?-alt-eq₁ (∘cxt (Γ₀ ++ A ∷ Ω)) Δ₁ [] | ++?-alt-eq₂ (∘fma A) (∘cxt Γ₀) (∘cxt Ω) Δ₁ | split-map-eq ∘fma Γ₀ (A ∷ Ω) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = Δ₁} _)
      (trans (runLeq ℓ)
             (cong (MMF.runLQ tt ℓ) (trans (only-lf⇑P-at≡ (_ ∷ ∘cxt Ω ++ ∘tcxt Δ₁) s _ lf₁ f done)
                                           (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = _ ∷ ∘cxt Ω ++ ∘tcxt Δ₁} _) (untag-seq≡ {Γ = ∘cxt (_ ∷ Ω) ++ ∘tcxt Δ₁}{_ ∷ ∘cxt Ω ++ ∘tcxt Δ₁} _ refl))))))))))
only-lf-fP-at≡ Δ₁ {x = x} s p lf (focl q lf₁ (unfoc ok f) eq₁ eq' ξ) eq ℓ = ⊥-elim (∙r⇑-at x f)
only-lf-fP-at≡ Δ₁ {x = x} s p lf (focr _ (⊗r+ Δ₀ Ξ m rf gs) f eq₁ eq' ξ) eq ℓ = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))
only-lf-fP-at≡ Δ₁ {X = ` X} s p lf (focr {Γ₁ = []} (just x) blurr (unfoc () f) eq₁ eq' ξ) eq ℓ

only-rf⇑N-at≡ : (Δ₀ : TCxt) {Δ₁ : Cxt} (Γ : Cxt) {B Q X : Fma} {x : isAt X}
  (n : isNeg (Γ ⊸⋆ B)) (q : isPosAt Q)
  (rf : just (Γ ⊸⋆ B , neg→negat n) MMF.⇛rf Δ₁ ； Q) 
  (f : (∘ , just X) MMF.∣ Δ₀ ++ ∘cxt Γ ⇑ (∘ , B)) → 
 ------------------------------------
  only-rf⇑N Δ₀ Γ n q rf f
    ≡ foc (at→negat x) q (focl (at→posat x) blurl (focr {Γ₁ = ∘cxt Δ₁} (just (_ , (neg→negat n))) rf (unfoc (inj₂ (x , n)) (MMF.⊸r⋆⇑ Γ (untag-seq {Γ = Δ₀ ++ ∘cxt Γ} f))) refl refl tt) refl refl tt)

only-rf-fN-at≡ : {Δ : TCxt} (Δ₀ : TCxt) {Δ₁ : Cxt} (Γ : Cxt) {Q Q' X : Fma} {x : isAt X}
  (n : isNeg (Γ ⊸⋆ Q')) (q : isPosAt Q) (q' : isPosAt Q')
  (rf : just (Γ ⊸⋆ Q' , neg→negat n) MMF.⇛rf Δ₁ ； Q) 
  (f : MMF.[ ∘ , ∘ ] (∘ , just X) ∣ Δ ⇓ (∘ , Q'))
  (eq : Δ ≡ Δ₀ ++ ∘cxt Γ) → 
 ------------------------------------
  only-rf-fN Δ₀ Γ (at→negat x) n q q' rf f eq
    ≡ focl (at→posat x) blurl (focr {Γ₁ = ∘cxt Δ₁} (just (_ , (neg→negat n))) rf (unfoc (inj₂ (x , n)) (MMF.⊸r⋆⇑ Γ (foc (at→negat x) q' (untag-seq-f {Γ = Δ₀ ++ ∘cxt Γ} (subst⇓ f eq))))) refl refl tt) refl refl tt

only-rf⇑N-at≡ Δ₀ Γ n q rf (⊸r f) =
  trans (only-rf⇑N-at≡ Δ₀ (Γ ∷ʳ _) n q rf f)
        (congfoc (congfocl refl (congfocr refl (cong (unfoc (inj₂ (_ , n))) (⊸r⋆⊸r⋆⇑ Γ (_ ∷ []) (untag-seq f))))))
only-rf⇑N-at≡ Δ₀ Γ {X = ` X} n q rf (foc s q₁ f) = 
  congfoc (only-rf-fN-at≡ Δ₀ Γ n q q₁ rf f refl)

only-rf-fN-at≡ Δ₀ Γ n q q' rf (focl {Γ₀ = []} q₁ blurl (focr (just (.(` _) , snd)) rf₁ ax refl refl ξ₁) refl refl ξ) refl = refl
only-rf-fN-at≡ Δ₀ Γ n q q' rf (focl {Γ₀ = _ ∷ _} q₁ blurl (focr (just (.(` _) , snd)) rf₁ ax refl refl ξ₁) refl () ξ) eq
only-rf-fN-at≡ Δ₀ Γ {X = ` X} n q q' rf (focl {Γ₀ = []} q₁ blurl (focr {Γ₀ = Γ₀} {Γ₁} (just x) rf₁ (unfoc ok f) refl refl ξ₁) refl refl ξ) eq with ++? Δ₀ [] (∘cxt Γ) (Γ₀ ++ Γ₁) eq
... | inj₂ (A , Ω , p , p') = ⊥-elim ([]disj∷ Δ₀ p)
... | inj₁ (.Δ₀ , p , refl) with ++? Δ₀ Γ₀ (∘cxt Γ) Γ₁ p
only-rf-fN-at≡ ._ Γ n q q' rf (focl {Γ₀ = []} q₁ blurl (focr {Γ₀ = Γ₀} (just (` X , m)) rf₁ (unfoc (inj₁ ()) f) refl refl ξ₁) refl refl ξ) refl | inj₁ (._ , p , refl) | inj₁ (Ω , refl , refl)
only-rf-fN-at≡ ._ Γ n q q' rf (focl {Γ₀ = []} q₁ blurl (focr {Γ₀ = Γ₀} (just (M ⊸ M₁ , m)) rf₁ (unfoc (inj₂ _) f) refl refl ξ₁) refl refl ξ) refl | inj₁ (._ , p , refl) | inj₁ (Ω , refl , refl)
  rewrite only-rf⇑N-at≡ (∘tcxt Γ₀) [] tt q' rf₁ f | untag-seq≡ {Γ = Γ₀}{Γ' = ∘tcxt Γ₀} f refl = refl
... | inj₂ (A , Ω , refl , eq') with split-map ∘fma Γ (A ∷ Ω) Γ₁ eq'
only-rf-fN-at≡ Δ₀ ._ n q q' rf (focl {Γ₀ = []} q₁ blurl (focr (just (` X , m)) rf₁ (unfoc (inj₁ ()) f) refl refl ξ₁) refl refl ξ) refl | inj₁ (.Δ₀ , p , refl) | inj₂ (._ , ._ , refl , eq') | _ ∷ Ω' , Γ₁' , refl , refl , refl
only-rf-fN-at≡ Δ₀ ._ n q q' rf (focl {Γ₀ = []} q₁ blurl (focr (just (M ⊸ M₁ , m)) rf₁ (unfoc (inj₂ _) f) refl refl ξ₁) refl refl ξ) refl | inj₁ (.Δ₀ , p , refl) | inj₂ (._ , ._ , refl , eq') | A ∷ Ω' , Γ₁' , refl , refl , refl =
  congfocl refl (congfocr refl (cong (unfoc (inj₂ (_ , tt))) (cong (MMF.⊸r⋆⇑ (_ ∷ Ω' ++ Γ₁'))
    (trans (only-rf⇑N-at≡ (∘tcxt Δ₀ ++ ∘cxt (A ∷ Ω')) [] tt q' rf₁ f)
           (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘tcxt Δ₀ ++ ∘cxt (A ∷ Ω')} (inj₂ (_ , tt))) (untag-seq≡ {Γ = Δ₀ ++ ∘cxt (A ∷ Ω')}{∘tcxt Δ₀ ++ ∘cxt (A ∷ Ω')} f refl)))))))))
only-rf-fN-at≡ Δ₀ Γ {x = x} n q q' rf (focl q₁ blurl (unfoc ok f) eq₁ eq' ξ) eq = ⊥-elim (pos×negat→⊥ ok (at→negat x))
only-rf-fN-at≡ Δ₀ Γ n q q' rf (focl {Γ₀ = x₁ ∷ Γ₀} q₁ blurl (focr (just x) rf₁ (unfoc ok f) refl refl ξ₁) refl () ξ) eq
only-rf-fN-at≡ Δ₀ Γ {x = x} n q q' rf (focr (just (M , m)) rf₁ (unfoc ok f) eq₁ eq' ξ) eq = ⊥-elim (∙l⇑-at x f)

only-rf⇑N-focl : {S : Stp} {Δ₀ : TCxt} {Λ Λ' Δ₁ : Cxt} (Γ : Cxt) {X Q R : Fma}
                 (s : isIrr S) (n : isNeg (Γ ⊸⋆ R)) (r : isPosAt R) (q : isPosAt Q) (x : isAt X)
                 {lf : at→posat x ⇛lf S ∣ Λ}
                 {rf : just (Γ ⊸⋆ R , neg→negat n) MMF.⇛rf Δ₁ ； Q}
               (f : MMF.[ ∙ , ∘ ] (∘ , just X) ∣ ∘cxt Λ' ++ ∘cxt Γ ⇓ (∘ , R))
               (eq : Δ₀ ≡ ∘cxt (Λ ++ Λ')) → 
            only-rf⇑N Δ₀ Γ n q rf (foc s r (focl {Γ₀ = ∘cxt Λ}{∘cxt (Λ' ++ Γ)} (at→posat x) lf f (cong (_++ ∘cxt Γ) {y = ∘cxt (Λ ++ Λ')} eq) refl tt))
              ≡ foc s q (focl {Γ₀ = ∘cxt Λ}{∘cxt (Λ' ++ Δ₁)} (at→posat x) lf (focr {Γ₀ = ∘cxt Λ'} {∘cxt Δ₁}_ rf (unfoc (inj₂ (x , n)) (MMF.⊸r⋆⇑ Γ (foc (at→negat x) r (focl {Γ₀ = []}{∘cxt (Λ' ++ Γ)} (at→posat x) blurl f refl refl tt)))) refl refl tt) (cong (_++ ∘cxt Δ₁) {y = ∘cxt (Λ ++ Λ')} eq) refl tt)

only-rf⇑N-focl {Λ = Λ} {Λ'} Γ s n r q x (focr (just (.(` _) , snd)) rf ax refl refl ξ) refl
  rewrite ++?-eq₁ (∘cxt Λ) (∘cxt Λ') (∘cxt Γ) = refl
only-rf⇑N-focl {Λ' = Λ'} Γ s n r q x (focr {Γ₀ = Γ₀} {Γ₁} (just x₁) rf (unfoc (inj₁ ok) f) eq refl ξ) refl = ⊥-elim (pos×negat→⊥ ok (at→negat x))
only-rf⇑N-focl {Λ' = Λ'} Γ {X = ` X} s n r q x (focr {Γ₀ = Γ₀} {Γ₁} (just x₁) rf (unfoc (inj₂ ok) f) eq refl ξ) refl with ++?-alt Γ₀ (∘cxt Λ') Γ₁ (∘cxt Γ) eq
... | inj₁ (Ω , eq' , refl) with split-map ∘fma Λ' Γ₀ Ω eq'
only-rf⇑N-focl {Λ = Λ} Γ s n r q x (focr {Γ₀ = .(map (λ A → ∘ , A) Γ₀')} {.(map (λ A → ∘ , A) Ω' ++ map _ Γ)} (just (_ ⊸ _ , m)) rf (unfoc (inj₂ (_ , n')) f) refl refl ξ) refl | inj₁ (.(map (λ A → ∘ , A) Ω') , eq' , refl) | Γ₀' , Ω' , refl , refl , refl
  rewrite ++?-eq₁ (∘cxt Λ) (∘cxt (Γ₀' ++ Ω')) (∘cxt Γ) | ++?-eq₁ (∘cxt Γ₀') (∘cxt Ω') (∘cxt Γ) =
    congfoc (congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ Γ)
      (trans (only-rf⇑N-at≡ (∘cxt Γ₀') [] tt r _ f)
             (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₀'} _) (untag-seq≡ {Γ = ∘cxt Γ₀'}{∘cxt Γ₀'} f refl))))))))))
only-rf⇑N-focl {Λ' = Λ'} Γ s n r q x (focr {Γ₀ = .(map (λ A₁ → ∘ , A₁) Λ' ++ A ∷ Ω)} {Γ₁} (just x₁) rf (unfoc (inj₂ ok) f) eq refl ξ) refl | inj₂ (A , Ω , refl , eq') with split-map ∘fma Γ (_ ∷ Ω) Γ₁ eq'
only-rf⇑N-focl {Λ = Λ}{Λ'} .((A' ∷ Ω') ++ Γ₁') {` _} s n r q x (focr {_} {_} {_} {_} {_} {.(map _ Λ' ++ (∘ , A') ∷ map (λ A → ∘ , A) Ω')} {.(map (λ A → ∘ , A) Γ₁')} (just (_ ⊸ _ , _)) rf (unfoc (inj₂ (_ , n')) f) refl refl ξ) refl | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Ω') , refl , eq') | A' ∷ Ω' , Γ₁' , refl , refl , refl
  rewrite ++?-eq₁ (∘cxt Λ) (∘cxt Λ') (∘cxt (A' ∷ Ω' ++ Γ₁')) | ++?-eq₂ (∘fma A') (∘cxt Λ') (∘cxt Ω') (∘cxt Γ₁') | split-map-eq ∘fma Ω' Γ₁' =
    congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Λ'} _) (cong (MMF.⊸r⋆⇑ {Γ = ∘cxt Λ'} (_ ∷ Ω' ++ Γ₁'))
      (trans (only-rf⇑N-at≡ (∘cxt (Λ' ++ A' ∷ Ω')) [] tt r rf f)
             (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (Λ' ++ A' ∷ Ω')} _) (untag-seq≡ {Γ = ∘cxt (Λ' ++ A' ∷ Ω')}{∘cxt (Λ' ++ A' ∷ Ω')} f refl ))))))))))
only-rf⇑N-focl Γ s n r q x (unfoc ok f) refl = ⊥-elim (pos×negat→⊥ ok (at→negat x))

{-
only-rf⇑N-focl' : {S : Stp} {Δ₀ : Cxt} {Λ Λ' Δ₁ : Cxt} (Γ : Cxt) {X Q R : Fma}
                 (s : isIrr S) (n : isNeg (Γ ⊸⋆ R)) (r : isPosAt R) (q : isPosAt Q) (x : isAt X)
                 {lf : at→posat x ⇛lf S ； Λ}
                 {rf : just (Γ ⊸⋆ R , neg→negat n) MMF.⇛rf Δ₁ ； Q}
               (f : MF.[ ∙ , ∘ ] just X ∣ Λ' ++  Γ ⇓ R)
               (eq : Δ₀ ≡ Λ ++ Λ') → 
            only-rf⇑N (∘cxt Δ₀) Γ n q rf (max {Γ = Δ₀ ++ Γ} (foc s r (focl {Γ₀ = Λ}{Λ' ++ Γ} (at→posat x) lf f (cong (_++ Γ) {y = Λ ++ Λ'} eq))))
              ≡ foc s q (focl {Γ₀ = ∘cxt Λ} {∘cxt (Λ' ++ Δ₁)} (at→posat x) (max-lf lf) (focr {Γ₀ = ∘cxt Λ'} {∘cxt Δ₁}_ rf (unfoc (inj₂ (x , n)) (MMF.⊸r⋆⇑ Γ (max {Γ = Λ' ++ Γ} (foc (at→negat x) r (focl {Γ₀ = []}{Λ' ++ Γ} (at→posat x) blurl f refl))))) refl refl tt) (cong (λ x → ∘cxt (x ++ Δ₁)) {y = Λ ++ Λ'} eq) refl tt)
only-rf⇑N-focl' {Λ = Λ} {Λ'} Γ s n r q x (focr (just (.(` _) , snd)) rf ax refl) refl
  rewrite ++?-eq₁ (∘cxt Λ) (∘cxt Λ') (∘cxt Γ) = refl
only-rf⇑N-focl' {Λ' = Λ'} Γ s n r q x (focr {Γ₀ = Γ₀} {Γ₁} (just x₁) rf (unfoc (inj₁ ok) f) eq) refl = ⊥-elim (pos×negat→⊥ ok (at→negat x))
only-rf⇑N-focl' {Λ' = Λ'} Γ {X = ` X} s n r q x (focr {Γ₀ = Γ₀} {Γ₁} (just x₁) rf (unfoc (inj₂ ok) f) eq) refl with ++?-alt Γ₀ Λ' Γ₁ Γ eq
only-rf⇑N-focl' {Λ = Λ} Γ {` X} s n r q x (focr {Γ₀ = Γ₀} {.(Ω ++ Γ)} (just (_ ⊸ _ , _)) rf (unfoc (inj₂ ok) f) refl) refl | inj₁ (Ω , refl , refl)
  rewrite ++?-eq₁ (∘cxt Λ) (∘cxt (Γ₀ ++ Ω)) (∘cxt Γ) | ++?-eq₁ (∘cxt Γ₀) (∘cxt Ω) (∘cxt Γ) = 
    congfoc (congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ Γ)
      (trans (only-rf⇑N-at≡ (∘cxt Γ₀) [] tt r _ _) 
             (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₀} _) (untag-seq≡ {Γ = ∘cxt Γ₀}{∘cxt Γ₀} _ refl))))))))))
only-rf⇑N-focl' {Λ = Λ} {Λ' = Λ'} .(A ∷ Ω ++ Γ₁) {` _} s n r q x (focr {Γ₀ = _} {Γ₁ = Γ₁} (just (_ ⊸ _ , _)) rf (unfoc (inj₂ ok) f) refl) refl | inj₂ (A , Ω , refl , refl) 
  rewrite ++?-eq₁ (∘cxt Λ) (∘cxt Λ') (∘cxt (A ∷ Ω ++ Γ₁)) | ++?-eq₂ (∘fma A) (∘cxt Λ') (∘cxt Ω) (∘cxt Γ₁) | split-map-eq ∘fma Ω Γ₁ = 
    congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Λ'} _) (cong (MMF.⊸r⋆⇑ {Γ = ∘cxt Λ'} (_ ∷ Ω ++ Γ₁))
      (trans (only-rf⇑N-at≡ (∘cxt (Λ' ++ A ∷ Ω)) [] tt r _ _)
             (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (Λ' ++ A ∷ Ω)} _) (untag-seq≡ {Γ = ∘cxt (Λ' ++ A ∷ Ω)}{∘cxt (Λ' ++ A ∷ Ω)} _ refl ))))))))))
only-rf⇑N-focl' Γ s n r q x (unfoc ok f) refl = ⊥-elim (pos×negat→⊥ ok (at→negat x))





max⊸r⋆⇑ : {S : Stp} {Γ : Cxt} (Δ : Cxt) {A : Fma}
      (f : S MF.∣ Γ ++ Δ ⇑ A) →
      max (MF.⊸r⋆⇑ Δ f) ≡ MMF.⊸r⋆⇑ Δ (max {Γ = Γ ++ Δ} f)
max⊸r⋆⇑ [] f = refl
max⊸r⋆⇑ {Γ = Γ} (A ∷ Δ) f = cong ⊸r (max⊸r⋆⇑ {Γ = Γ ∷ʳ A} Δ f)

-- cong-only-rf⇑ : ∀ {S Δ₀ Δ₁ M Q m q}
--               {rf : just (M , m) MMF.⇛rf Δ₁ ； Q}
--               {f g : (∘ , S) MMF.∣ Δ₀ ⇑ (∘ , M)} → f ≡ g → 
--               only-rf⇑ Δ₀ m q rf f ≡  only-rf⇑ Δ₀ m q rf g             
-- cong-only-rf⇑ refl = refl
-}

only-rf⇑++ : ∀ {S Δ₀ Δ₁} Γ Γ' {A Q}
                {m : isNeg ((Γ ++ Γ') ⊸⋆ A)} {q : isPosAt Q}
                {rf : just ((Γ ++ Γ') ⊸⋆ A , neg→negat m) MMF.⇛rf Δ₁ ； Q}
                (f : (∘ , S) MMF.∣ Δ₀ ++ ∘cxt (Γ ++ Γ') ⇑ (∘ , A)) →
                only-rf⇑N Δ₀ (Γ ++ Γ') m q rf f ≡ only-rf⇑N Δ₀ Γ m q rf (MMF.⊸r⋆⇑ Γ' f)
only-rf⇑++ Γ [] f = refl
only-rf⇑++ Γ (A' ∷ Γ') f = only-rf⇑++ (Γ ∷ʳ A') Γ' f

r∙→∘⇑-runLQ : ∀ {S Γ Δ A Q} {q : isPosAt Q} (ℓ : MF.L S Γ A)
  → (f : (∘ , S) MMF.∣ ∙cxt Γ ++ Δ ⇑ (∙ , Q))
  → r∙→∘⇑ {Γ = Δ} (MMF.runLQ q ℓ f) ≡ MMF.runLQ q ℓ (r∙→∘⇑ {Γ = ∙cxt Γ ++ Δ} f)
r∙→∘⇑-runLQ done f = refl
r∙→∘⇑-runLQ (Il-1 ℓ) f = r∙→∘⇑-runLQ ℓ (Il _ f)
r∙→∘⇑-runLQ (⊗l-1 ℓ) f = r∙→∘⇑-runLQ ℓ (⊗l _ f)

only-rf⇑-at-runLQ : {S : Stp} {Δ₀ : TCxt} {Γ Δ₁ : Cxt} {X Q A : Fma}
               {x : isAt X} {q : isPosAt Q}
               {rf : just (X , at→negat x) MMF.⇛rf Δ₁ ； Q}
               (f : (∘ , S) MMF.∣ ∘cxt Γ ++ Δ₀ ⇑ (∘ , X))
               (ℓ : L S Γ A) →
               only-rf⇑-at Δ₀ x q rf (MMF.runLQ (at→posat x) ℓ f)
                 ≡ MMF.runLQ q ℓ (only-rf⇑-at (∘cxt Γ ++ Δ₀) x q rf f)
only-rf⇑-at-runLQ f done = refl
only-rf⇑-at-runLQ f (Il-1 ℓ) = only-rf⇑-at-runLQ (Il _ f) ℓ
only-rf⇑-at-runLQ f (⊗l-1 ℓ) = only-rf⇑-at-runLQ (⊗l _ f) ℓ

only-lf⇑-⊸r⋆⇑ : {S : Stp} {Δ₀ : Cxt} (Δ₁ : TCxt) (Δ : Cxt) {C Q : Fma}
               {s : isIrr S} {q : isPosAt Q}
               {lf : q ⇛lf S ∣ Δ₀}
               (f : (∘ , just Q) MMF.∣ Δ₁ ++ ∘cxt Δ ⇑ (∘ , C)) →
               only-lf⇑ Δ₁ s q lf (MMF.⊸r⋆⇑ Δ f) ≡ MMF.⊸r⋆⇑ Δ (only-lf⇑ (Δ₁ ++ ∘cxt Δ) s q lf f)
only-lf⇑-⊸r⋆⇑ Δ₁ [] f = refl
only-lf⇑-⊸r⋆⇑ Δ₁ (_ ∷ Δ) {Q = ` X} f = cong ⊸r (only-lf⇑-⊸r⋆⇑ (Δ₁ ∷ʳ _) Δ f)
only-lf⇑-⊸r⋆⇑ Δ₁ (_ ∷ Δ) {Q = I} f = cong ⊸r (only-lf⇑-⊸r⋆⇑ (Δ₁ ∷ʳ _) Δ f)
only-lf⇑-⊸r⋆⇑ Δ₁ (_ ∷ Δ) {Q = A ⊗ B} f = cong ⊸r (only-lf⇑-⊸r⋆⇑ (Δ₁ ∷ʳ _) Δ f)


only-rf⇑N-Il⇑ : (Δ₀ : TCxt) {Δ₁ : Cxt} (Γ : Cxt) {B Q : Fma}
                {n : isNeg (Γ ⊸⋆ B)} {q : isPosAt Q}
                {rf : just (Γ ⊸⋆ B , neg→negat n) MMF.⇛rf Δ₁ ； Q}
                (f : (∘ , ─) MMF.∣ Δ₀ ++ ∘cxt Γ ⇑ (∘ , B)) →
                only-rf⇑N Δ₀ Γ n q rf (MMF.Il⇑ f) ≡ MMF.Il⇑ (only-rf⇑N Δ₀ Γ n q rf f)
only-rf⇑N-Il⇑ Δ₀ Γ (⊸r f) = only-rf⇑N-Il⇑ Δ₀ (Γ ∷ʳ _) f
only-rf⇑N-Il⇑ _ _ (foc s q f) = refl

only-rf⇑-Il⇑ : ∀ {Δ₀ Δ₁ M Q m q}
                 {rf : just (M , m) MMF.⇛rf Δ₁ ； Q}
                 (f : (∘ , ─) MMF.∣ Δ₀ ⇑ (∘ , M)) →
                 only-rf⇑ Δ₀ m q rf (MMF.Il⇑ f) ≡ MMF.Il⇑ (only-rf⇑ Δ₀ m q rf f)
only-rf⇑-Il⇑ {M = ` X} (foc s q f) = refl
only-rf⇑-Il⇑ {M = A ⊸ B} f = only-rf⇑N-Il⇑ _ [] f

only-rf⇑N-⊗l⇑ : (Δ₀ : TCxt) {Δ₁ : Cxt} (Γ : Cxt) {A' B' B Q : Fma}
                {n : isNeg (Γ ⊸⋆ B)} {q : isPosAt Q}
                {rf : just (Γ ⊸⋆ B , neg→negat n) MMF.⇛rf Δ₁ ； Q}
                (f : (∘ , just A') MMF.∣ ∘fma B' ∷ Δ₀ ++ ∘cxt Γ ⇑ (∘ , B)) →
                only-rf⇑N Δ₀ Γ n q rf (MMF.⊗l⇑ f) ≡ MMF.⊗l⇑ (only-rf⇑N (∘fma B' ∷ Δ₀) Γ n q rf f)
only-rf⇑N-⊗l⇑ Δ₀ Γ (⊸r f) = only-rf⇑N-⊗l⇑ Δ₀ (Γ ∷ʳ _) f
only-rf⇑N-⊗l⇑ _ _ (Il q f) = refl
only-rf⇑N-⊗l⇑ _ Γ (⊗l q f) = cong (⊗l _) (only-rf⇑N-⊗l⇑ _ Γ f)
only-rf⇑N-⊗l⇑ _ _ (foc s q f) = refl

only-rf⇑-⊗l⇑ : ∀ {Δ₀ Δ₁ A' B' M Q m q}
                 {rf : just (M , m) MMF.⇛rf Δ₁ ； Q}
                 (f : (∘ , just A') MMF.∣ ∘fma B' ∷ Δ₀ ⇑ (∘ , M)) →
                 only-rf⇑ Δ₀ m q rf (MMF.⊗l⇑ f) ≡ MMF.⊗l⇑ (only-rf⇑ (∘fma B' ∷ Δ₀) m q rf f)
only-rf⇑-⊗l⇑ {M = ` X} (Il q f) = refl
only-rf⇑-⊗l⇑ {M = ` X} (⊗l q f) = cong (⊗l _) (only-rf⇑-⊗l⇑ {M = ` X} f)
only-rf⇑-⊗l⇑ {M = ` X} (foc s q f) = refl
only-rf⇑-⊗l⇑ {M = A ⊸ B} f = only-rf⇑N-⊗l⇑ _ [] f

only-rf⇑-runL : ∀ {S Γ Δ₀ Δ₁ A M Q m q}
                 {rf : just (M , m) MMF.⇛rf Δ₁ ； Q}
                 (f : (∘ , S) MMF.∣ ∘cxt Γ ++ Δ₀ ⇑ (∘ , M))
                 (ℓ : L S Γ A) → 
                 only-rf⇑ Δ₀ m q rf (MMF.runL ℓ f) ≡ MMF.runLQ q ℓ (only-rf⇑ (∘cxt Γ ++ Δ₀) m q rf f)
only-rf⇑-runL f done = refl
only-rf⇑-runL f (Il-1 ℓ) =
  trans (only-rf⇑-runL (MMF.Il⇑ f) ℓ)
        (cong (MMF.runLQ _ ℓ) (trans (only-rf⇑-Il⇑ f) (Il⇑eq _)))
only-rf⇑-runL f (⊗l-1 ℓ) = 
  trans (only-rf⇑-runL (MMF.⊗l⇑ f) ℓ)
        (cong (MMF.runLQ _ ℓ) (trans (only-rf⇑-⊗l⇑ f) (⊗l⇑eq _)))

ltag-∘cxt : (Γ : Cxt) → ltag (∘cxt Γ) ∙ → ⊥
ltag-∘cxt (A ∷ Γ) ξ = ltag-∘cxt Γ ξ

isProp-ltag : {Γ : TCxt} {t : Tag} (ξ ξ' : ltag Γ t) → ξ ≡ ξ'
isProp-ltag {t = ∘} ξ ξ' = refl
isProp-ltag {(∘ , A) ∷ Γ} {∙} ξ ξ' = isProp-ltag {Γ} {∙} ξ ξ'
isProp-ltag {(∙ , A) ∷ Γ} {∙} ξ ξ' = refl

only-rf⇑N-l∙ : {S : Stp} {Δ₀ : Cxt} {Δ₁ : Cxt} {Γ : Cxt} {B Q : Fma}
               {s : isIrr S} {n : isNeg (Γ ⊸⋆ B)} {q : isPosAt Q}
               {rf : just (Γ ⊸⋆ B , neg→negat n) MMF.⇛rf Δ₁ ； Q}
               (f : (∙ , S) MMF.∣ ∘cxt Δ₀ ++ ∙cxt Γ ⇑ (∘ , B)) → 
              ------------------------------------
             only-rf⇑N (∘cxt Δ₀) Γ n q rf (l∙→∘⇑ {Γ = ∘cxt Δ₀ ++ ∙cxt Γ} f)
               ≡ foc s q (focr {Γ₀ = ∘cxt Δ₀} {∘cxt Δ₁} _ rf (unfoc n (MMF.⊸r⋆⇑ Γ f)) refl refl tt)

only-rf⇑N-l∙ {Γ = Γ} (⊸r f) =
  trans (only-rf⇑N-l∙ {Γ = Γ ∷ʳ _} f)
        (congfoc (congfocr refl (cong (unfoc _) (⊸r⋆⊸r⋆⇑ Γ (_ ∷ []) f))))
only-rf⇑N-l∙ {Δ₀ = Δ₀} {Γ = Γ} (foc s q (focl {Γ₀ = Γ₀} {Γ₁} q₁ lf (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) eq refl ξ)) with ++?-alt Γ₀ (∘cxt Δ₀) Γ₁ (∙cxt Γ) eq
... | inj₁ (Λ , eq' , refl) with split-map ∘fma Δ₀ Γ₀ Λ eq'
only-rf⇑N-l∙ {Δ₀ = .(Γ₀' ++ Λ')} {Γ = Γ} (foc s q (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₀')} {.(map (λ A → ∘ , A) Λ' ++ map _ Γ)} q₁ lf (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) refl refl ξ)) | inj₁ (.(map (λ A → ∘ , A) Λ') , eq' , refl) | Γ₀' , Λ' , refl , refl , refl = ⊥-elim (ltag-∘cxt Γ₀' ξ)
only-rf⇑N-l∙ {S} {Δ₀ = Δ₀} {Γ = Γ} (foc s q (focl {Γ₀ = .(map (λ A₁ → ∘ , A₁) Δ₀ ++ A ∷ Λ)} {Γ₁} q₁ lf (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) eq refl ξ)) | inj₂ (A , Λ , refl , eq') with split-map ∙fma Γ (_ ∷ Λ) Γ₁ eq'
only-rf⇑N-l∙ {S} {Δ₀ = Δ₀} {Γ = .((A' ∷ Λ') ++ Γ₁')} {s = s'} (foc s q (focl {_} {_} {_} {_} {.(map _ Δ₀ ++ (∙ , A') ∷ map (λ A → ∙ , A) Λ')} {.(map (λ A → ∙ , A) Γ₁')} q₁ lf (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) refl refl ξ)) | inj₂ (.(∙ , A') , .(map (λ A → ∙ , A) Λ') , refl , eq') | A' ∷ Λ' , Γ₁' , refl , refl , refl
  rewrite ++?-eq₂ (∘fma A') (∘cxt Δ₀) (∘cxt Λ') (∘cxt Γ₁') | split-map-eq ∘fma Λ' Γ₁' | isProp-isIrr {S} s s' | isProp-ltag {∘cxt Δ₀ ++ ∙cxt (A' ∷ Λ')} {∙} ξ (ltag++ (∘cxt Δ₀)) = refl
only-rf⇑N-l∙ {Δ₀ = Δ₀} {Γ = Γ} (foc s q (focl {Γ₀ = Γ₀} q₁ lf (focr {Γ₀ = Γ₁}{Γ₂} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) eq refl ξ)) with ++?-alt Γ₀ (∘cxt Δ₀) (Γ₁ ++ Γ₂) (∙cxt Γ) eq
... | inj₁ (Λ , eq' , eq'') with split-map ∘fma Δ₀ Γ₀ Λ eq'
... | (Γ₀' , Λ' , refl , refl , refl) = ⊥-elim (ltag-∘cxt Γ₀' ξ)
only-rf⇑N-l∙ {S} {Δ₀ = Δ₀} {Γ = Γ} (foc s q (focl {Γ₀ = .(map (λ A₁ → ∘ , A₁) Δ₀ ++ A ∷ Λ)} q₁ lf (focr {Γ₀ = Γ₁} {Γ₂} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) eq refl ξ)) | inj₂ (A , Λ , refl , eq') with split-map ∙fma Γ (_ ∷ Λ) (Γ₁ ++ Γ₂) eq'
... | A' ∷ Λ' , Ω , refl , eq' , refl with split-map ∙fma Ω Γ₁ Γ₂ eq'
only-rf⇑N-l∙ {S} {Δ₀ = Δ₀} {_} {.((A' ∷ Λ') ++ Γ₁' ++ Γ₂')} {s = s'} (foc s q (focl {_} {_} {_} {_} {.(map _ Δ₀ ++ (∙ , A') ∷ map _ Λ')} q₁ lf (focr {Γ₀ = .(map (λ A → ∙ , A) Γ₁')} {.(map (λ A → ∙ , A) Γ₂')} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ)) | inj₂ (.(∙ , A') , .(map _ Λ') , refl , eq'') | A' ∷ Λ' , .(Γ₁' ++ Γ₂') , refl , eq' , refl | Γ₁' , Γ₂' , refl , refl , refl
  rewrite ++?-eq₂ (∘fma A') (∘cxt Δ₀) (∘cxt Λ') (∘cxt (Γ₁' ++ Γ₂')) | split-map-eq ∘fma Λ' (Γ₁' ++ Γ₂') | split-map-eq ∘fma Γ₁' Γ₂' | isProp-isIrr {S} s s' | isProp-ltag {∘cxt Δ₀ ++ ∙cxt (A' ∷ Λ')} {∙} ξ (ltag++ (∘cxt Δ₀)) = refl
only-rf⇑N-l∙ {Δ₀ = Δ₀} {Γ = Γ} (foc s q (focl {Γ₀ = Γ₀} {Γ₁} q₁ lf (unfoc ok f) eq refl ξ)) with ++?-alt Γ₀ (∘cxt Δ₀) Γ₁ (∙cxt Γ) eq
... | inj₁ (Λ , eq' , refl) with split-map ∘fma Δ₀ Γ₀ Λ eq'
only-rf⇑N-l∙ {Δ₀ = .(Γ₀' ++ Λ')} {Γ = Γ} (foc s q (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₀')} {.(map (λ A → ∘ , A) Λ' ++ map _ Γ)} q₁ lf (unfoc ok f) refl refl ξ)) | inj₁ (.(map (λ A → ∘ , A) Λ') , eq' , refl) | Γ₀' , Λ' , refl , refl , refl = ⊥-elim (ltag-∘cxt Γ₀' ξ)
only-rf⇑N-l∙ {S} {Δ₀ = Δ₀} {Γ = Γ} (foc s q (focl {Γ₀ = .(map (λ A₁ → ∘ , A₁) Δ₀ ++ A ∷ Λ)} {Γ₁} q₁ lf (unfoc ok f) eq refl ξ)) | inj₂ (A , Λ , refl , eq') with split-map ∙fma Γ (_ ∷ Λ) Γ₁ eq'
only-rf⇑N-l∙ {S} {Δ₀ = Δ₀} {Γ = .((A' ∷ Λ') ++ Γ₁')} {s = s'} (foc s q (focl {_} {_} {_} {_} {.(map _ Δ₀ ++ (∙ , A') ∷ map (λ A → ∙ , A) Λ')} {.(map (λ A → ∙ , A) Γ₁')} q₁ lf (unfoc ok f) refl refl ξ)) | inj₂ (.(∙ , A') , .(map (λ A → ∙ , A) Λ') , refl , eq') | A' ∷ Λ' , Γ₁' , refl , refl , refl
  rewrite ++?-eq₂ (∘fma A') (∘cxt Δ₀) (∘cxt Λ') (∘cxt Γ₁') | split-map-eq ∘fma Λ' Γ₁' | isProp-isIrr {S} s s' | isProp-ltag {∘cxt Δ₀ ++ ∙cxt (A' ∷ Λ')} {∙} ξ (ltag++ (∘cxt Δ₀)) = refl
only-rf⇑N-l∙ {Δ₀ = Δ₀} {Γ = Γ} (foc s q (focr {Γ₀ = Γ₀} {Γ₁} (just x) rf (unfoc ok f) eq refl ξ)) with ++?-alt Γ₀ (∘cxt Δ₀) Γ₁ (∙cxt Γ) eq
... | inj₁ (Λ , eq' , refl) with split-map ∘fma Δ₀ Γ₀ Λ eq'
only-rf⇑N-l∙ {S} {Δ₀ = .(Γ₀' ++ Λ')} {Γ = Γ} {s = s'} (foc s q (focr (just x) rf (unfoc ok f) refl refl ξ)) | inj₁ (.(map (λ A → ∘ , A) Λ') , eq' , refl) | Γ₀' , Λ' , refl , refl , refl
  rewrite ++?-eq₁ (∘cxt Γ₀') (∘cxt Λ') (∘cxt Γ) | isProp-isIrr {S} s s' = refl
only-rf⇑N-l∙ {S} {Δ₀ = Δ₀} {Γ = Γ} (foc s q (focr {Γ₁ = Γ₁} (just x) rf (unfoc ok f) eq refl ξ)) | inj₂ (A , Λ , refl , eq') with split-map ∙fma Γ (_ ∷ Λ) Γ₁ eq'
only-rf⇑N-l∙ {S} {Δ₀ = Δ₀} {Γ = .((A' ∷ Λ') ++ Γ₁')} {s = s'} (foc s q (focr (just x) rf (unfoc ok f) refl refl ξ)) | inj₂ (.(∙ , A') , .(map (λ A → ∙ , A) Λ') , refl , eq') | A' ∷ Λ' , Γ₁' , refl , refl , refl
  rewrite ++?-eq₂ (∘fma A') (∘cxt Δ₀) (∘cxt Λ') (∘cxt Γ₁') | split-map-eq ∘fma Λ' Γ₁' | isProp-isIrr {S} s s' = refl
only-rf⇑N-l∙ (foc s q (focr ─ rf (refl , refl) refl refl ξ)) = refl


⊸r⋆Il⇑ : ∀ {Γ} Δ {A}
         {f : (∘ , ─) MMF.∣ Γ ++ ∘cxt Δ ⇑ (∘ , A)} →
         MMF.⊸r⋆⇑ Δ (MMF.Il⇑ f) ≡ MMF.Il⇑ (MMF.⊸r⋆⇑ Δ f)
⊸r⋆Il⇑ [] = refl
⊸r⋆Il⇑ (_ ∷ Δ) = cong ⊸r (⊸r⋆Il⇑ Δ)

⊸r⋆⊗l⇑ : ∀ {Γ} Δ {A A' B'}
         {f : (∘ , just A') MMF.∣ ∘fma B' ∷ Γ ++ ∘cxt Δ ⇑ (∘ , A)} →
         MMF.⊸r⋆⇑ Δ (MMF.⊗l⇑ f) ≡ MMF.⊗l⇑ (MMF.⊸r⋆⇑ Δ f)
⊸r⋆⊗l⇑ [] = refl
⊸r⋆⊗l⇑ (_ ∷ Δ) = cong ⊸r (⊸r⋆⊗l⇑ Δ)

⊸r⋆runL : ∀ {S Γ₀ Γ₁} Δ {A Q} 
         {f : (∘ , S) MMF.∣ ∘cxt Γ₀ ++ Γ₁ ++ ∘cxt Δ ⇑ (∘ , Q)}
         (ℓ : L S Γ₀ A) →
         MMF.⊸r⋆⇑ Δ (MMF.runL {Δ = Γ₁ ++ ∘cxt Δ} ℓ f) ≡ MMF.runL {Δ = Γ₁} ℓ (MMF.⊸r⋆⇑ Δ f)
⊸r⋆runL Δ done = refl
⊸r⋆runL Δ (Il-1 ℓ) = trans (⊸r⋆runL Δ ℓ) (cong (MMF.runL ℓ) (⊸r⋆Il⇑ Δ)) 
⊸r⋆runL Δ (⊗l-1 ℓ) = trans (⊸r⋆runL Δ ℓ) (cong (MMF.runL ℓ) (⊸r⋆⊗l⇑ Δ)) 

only-rf-f-lf-f-at : ∀ {S} Γ₀ Γ₁ Γ₂ Δ {X Q R}
  {s : isIrr S} {x : isAt X} {n : isNeg (Δ ⊸⋆ R)} {q : isPosAt Q} {r : isPosAt R}
  {lf : at→posat x ⇛lf S ∣ Γ₀}
  {rf : just (Δ ⊸⋆ R , neg→negat n) MMF.⇛rf Γ₂ ； Q}
  (f : MMF.[ ∘ , ∘ ] (∘ , just X) ∣ ∘cxt Γ₁ ++ ∘cxt Δ ⇓ (∘ , R)) → 
  only-rf-fN (∘cxt (Γ₀ ++ Γ₁)) Δ s n q r rf (only-lf-f-at (∘cxt (Γ₁ ++ Δ)) s x lf f) refl  
    ≡ focl {Γ₀ = ∘cxt Γ₀} (at→posat x) lf (focr {Γ₀ = ∘cxt Γ₁} {Γ₁ = ∘cxt Γ₂} (just (Δ ⊸⋆ R , neg→negat n)) rf (unfoc (inj₂ (x , n)) (MMF.⊸r⋆⇑ Δ (foc (at→negat x) r f))) refl refl tt) refl refl tt
only-rf-f-lf-f-at Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = []} q blurl (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) refl refl ξ)
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt Δ) = refl
only-rf-f-lf-f-at Γ₀ Γ₁ Γ₂ Δ {X = ` X} (focl {Γ₀ = []} q blurl (focr {Γ₀ = Λ₀}{Λ₁} (just x) rf (unfoc (inj₂ (_ , n)) f) refl refl ξ₁) eq refl ξ) with ++?-alt Λ₀ (∘cxt Γ₁) Λ₁ (∘cxt Δ) eq
... | inj₁ (Ω , eq' , refl) with split-map ∘fma Γ₁ Λ₀ Ω eq'
only-rf-f-lf-f-at Γ₀ .(Λ₀ ++ Ω) Γ₂ Δ (focl {_} {_} {_} {_} {[]} q blurl (focr {Γ₀ = .(map (λ A → ∘ , A) Λ₀)} {.(map (λ A → ∘ , A) Ω ++ map _ Δ)} (just (_ ⊸ _ , m)) rf (unfoc (inj₂ (_ , n)) f) refl refl ξ₁) refl refl ξ) | inj₁ (.(map (λ A → ∘ , A) Ω) , eq' , refl) | Λ₀ , Ω , refl , refl , refl
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt (Λ₀ ++ Ω)) (∘cxt Δ) | ++?-eq₁ (∘cxt Λ₀) (∘cxt Ω) (∘cxt Δ) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (Λ₀ ++ Ω)} _) (cong (MMF.⊸r⋆⇑ Δ)
      (trans (only-rf⇑N-at≡ (∘cxt Λ₀) [] tt _ _ f)
             (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Λ₀} _) (untag-seq≡ {Γ = ∘cxt Λ₀}{∘cxt Λ₀} _ refl)))))))))
only-rf-f-lf-f-at {S} Γ₀ Γ₁ Γ₂ Δ (focl {_} {_} {_} {_} {[]} q blurl (focr {Γ₀ = .(map (λ A₁ → ∘ , A₁) Γ₁ ++ A ∷ Ω)} {Λ₁} (just (_ ⊸ _ , m)) rf (unfoc (inj₂ (_ , n)) f) refl refl ξ₁) eq refl ξ) | inj₂ (A , Ω , refl , eq') with split-map ∘fma Δ (_ ∷ Ω) Λ₁ eq'
only-rf-f-lf-f-at {S} Γ₀ Γ₁ Γ₂ .((_ ∷ Ω') ++ Λ₁') {` _} (focl {_} {_} {_} {_} {[]} q blurl (focr {_} {_} {_} {_} {_} {.(map _ Γ₁ ++ (∘ , _) ∷ map (λ A → ∘ , A) Ω')} {.(map (λ A → ∘ , A) Λ₁')} (just x) rf (unfoc (inj₂ (_ , n)) f) refl refl ξ₁) refl refl ξ) | inj₂ (.(∘ , _) , .(map (λ A → ∘ , A) Ω') , refl , eq') | A' ∷ Ω' , Λ₁' , refl , refl , refl
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt (A' ∷ Ω' ++ Λ₁')) | ++?-eq₂ (∘fma A') (∘cxt Γ₁) (∘cxt Ω') (∘cxt Λ₁') | split-map-eq ∘fma Ω' Λ₁' =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (cong (MMF.⊸r⋆⇑ (_ ∷ Ω' ++ Λ₁'))
      (trans (only-rf⇑N-at≡ (∘cxt (Γ₁ ++ _ ∷ Ω')) [] tt _ _ f)
             (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (Γ₁ ++ _ ∷ Ω')} _) (untag-seq≡ {Γ = ∘cxt (Γ₁ ++ _ ∷ Ω')}{∘cxt (Γ₁ ++ _ ∷ Ω')} _ refl)))))))))
only-rf-f-lf-f-at Γ₀ Γ₁ Γ₂ Δ {X = ` X} (focl {Γ₀ = []} q blurl (unfoc () f) eq refl ξ) 
only-rf-f-lf-f-at Γ₀ Γ₁ Γ₂ Δ {x = x} (focr (just _) rf (unfoc ok f) eq refl ξ) = ⊥-elim (∙l⇑-at x f)

only-rf⇑N-lf⇑-at : ∀ {S} Γ₀ Γ₁ Γ₂ Δ {X Q R}
  {s : isIrr S} {x : isAt X} {n : isNeg (Δ ⊸⋆ R)} {q : isPosAt Q}
  {lf : at→posat x ⇛lf S ∣ Γ₀}
  {rf : just (Δ ⊸⋆ R , neg→negat n) MMF.⇛rf Γ₂ ； Q}
  (f : (∘ , just X) MMF.∣ ∘cxt Γ₁ ++ ∘cxt Δ ⇑ (∘ , R)) → 
  only-rf⇑N (∘cxt (Γ₀ ++ Γ₁)) Δ n q rf (only-lf⇑-at (∘cxt (Γ₁ ++ Δ)) s x lf f)  
    ≡ foc s q (focl {Γ₀ = ∘cxt Γ₀} (at→posat x) lf (focr {Γ₀ = ∘cxt Γ₁} {Γ₁ = ∘cxt Γ₂} (just (Δ ⊸⋆ R , neg→negat n)) rf (unfoc (inj₂ (x , n)) (MMF.⊸r⋆⇑ Δ f)) refl refl tt) refl refl tt)
only-rf⇑N-lf⇑-at Γ₀ Γ₁ Γ₂ Δ (⊸r f) =
  trans (only-rf⇑N-lf⇑-at Γ₀ Γ₁ Γ₂ (Δ ∷ʳ _) f)
        (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (⊸r⋆⊸r⋆⇑ Δ (_ ∷ []) _)))))
only-rf⇑N-lf⇑-at Γ₀ Γ₁ Γ₂ Δ {` X} {q = q} (foc s r f) =
  congfoc (only-rf-f-lf-f-at Γ₀ Γ₁ Γ₂ Δ {q = q} f)

only-rf-f-at-lf-fP : ∀ {S' S Γ' Γ} Γ₀ Γ₁ Γ₂ {X Q P} 
  {s : isIrr S'} {p : isPos P} {x : isAt X} {q : isPosAt Q}
  {lf : pos→posat p ⇛lf S ∣ Γ₀}
  {rf : just (X , at→negat x) MMF.⇛rf Γ₂ ； Q}
  (f : MMF.[ ∘ , ∘ ] (∘ , S') ∣ Γ' ⇓ (∘ , X))
  (eq : Γ' ≡ ∘cxt (Γ ++ Γ₁))
  (ℓ : L S' Γ P) → 
  only-rf-f-at (∘cxt (Γ₀ ++ Γ₁)) x q rf (only-lf-fP (∘cxt Γ₁) s p (at→posat x) lf f eq ℓ)
    ≡ focl {Γ₀ = ∘cxt Γ₀} (pos→posat p) lf (focr {Γ₀ = ∘cxt Γ₁} {∘cxt Γ₂} (just _) rf (unfoc (inj₁ p) (MMF.runLQ (at→posat x) ℓ (foc s (at→posat x) (subst⇓ f eq)))) refl refl tt) refl refl tt

only-rf⇑-at-lf⇑P : ∀ {S' S Γ} Γ₀ Γ₁ Γ₂ {X Q P} 
  {s : isIrr S} {p : isPos P} {x : isAt X} {q : isPosAt Q}
  {lf : pos→posat p ⇛lf S ∣ Γ₀}
  {rf : just (X , at→negat x) MMF.⇛rf Γ₂ ； Q}
  (f : (∘ , S') MMF.∣ ∘cxt (Γ ++ Γ₁) ⇑ (∘ , X))
  (ℓ : L S' Γ P) → 
  only-rf⇑-at (∘cxt (Γ₀ ++ Γ₁)) x q rf (only-lf⇑P (∘cxt Γ₁) s p lf f ℓ)
    ≡ foc s q (focl {Γ₀ = ∘cxt Γ₀} (pos→posat p) lf (focr {Γ₀ = ∘cxt Γ₁} {∘cxt Γ₂} (just _) rf (unfoc (inj₁ p) (MMF.runLQ (at→posat x) ℓ f)) refl refl tt) refl refl tt)

only-rf⇑-at-lf⇑P Γ₀ Γ₁ Γ₂ {` X} (Il q f) ℓ = only-rf⇑-at-lf⇑P Γ₀ Γ₁ Γ₂ f (Il-1 ℓ)
only-rf⇑-at-lf⇑P Γ₀ Γ₁ Γ₂ {` X} (⊗l q f) ℓ = only-rf⇑-at-lf⇑P Γ₀ Γ₁ Γ₂ f (⊗l-1 ℓ)
only-rf⇑-at-lf⇑P Γ₀ Γ₁ Γ₂ {` X} {q = q} (foc s _ f) ℓ = congfoc (only-rf-f-at-lf-fP Γ₀ Γ₁ Γ₂ {q = q} f refl ℓ)

only-rf-f-at-lf-fP Γ₀ Γ₁ Γ₂ {x = x} (focl q lf (focr (just _) (⊗r+ Δ₀ Ξ m rf gs) f eq₂ eq'' ξ₁) eq₁ eq' ξ) eq ℓ = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))
only-rf-f-at-lf-fP {Γ = Γ} Γ₀ Γ₁ Γ₂ {x = x} (focl q lf (focr {Γ₁ = []} (just (.(` _) , tt)) blurr ax refl refl ξ₁) refl refl ξ) refl ℓ
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt Γ₁) [] = refl
only-rf-f-at-lf-fP {Γ = Γ} Γ₀ Γ₁ Γ₂ (focl {Γ₀ = Λ₀}{Λ₁} q lf (focr {Γ₁ = []} (just (M , m)) blurr (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ with ++?-alt (∘cxt Γ) Λ₀ (∘cxt Γ₁) Λ₁ eq
... | inj₁ (Ω , refl , eq') with split-map ∘fma Γ₁ Ω Λ₁ eq'
only-rf-f-at-lf-fP {Γ = Γ} Γ₀ .(Ω ++ Λ₁) Γ₂ (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ A → ∘ , A) Ω)} {.(map (λ A → ∘ , A) Λ₁)} {Q = I} q lf (focr {_} {_} {_} {_} {_} {_} {[]} (just (` X , _)) blurr (unfoc (inj₁ p) f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ A → ∘ , A) Ω) , refl , eq') | Ω , Λ₁ , refl , refl , refl 
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt (Ω ++ Λ₁)) [] | ++?-alt-eq₁ (∘cxt Γ) (∘cxt Ω) (∘cxt Λ₁) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (Ω ++ Λ₁)} _)
             (trans (runLeq ℓ)
                    (cong (MMF.runLQ tt ℓ) (trans (only-lf⇑P-at≡ (∘cxt Λ₁) _ _ lf f done)
                                                  (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Λ₁} _) (untag-seq≡ {Γ = ∘cxt Λ₁}{∘cxt Λ₁} _ refl))))))))))             
only-rf-f-at-lf-fP {Γ = Γ} Γ₀ .(Ω ++ Λ₁) Γ₂ (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ A → ∘ , A) Ω)} {.(map (λ A → ∘ , A) Λ₁)} {Q = _ ⊗ _} q lf (focr {_} {_} {_} {_} {_} {_} {[]} (just (` X , _)) blurr (unfoc (inj₁ p) f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ A → ∘ , A) Ω) , refl , eq') | Ω , Λ₁ , refl , refl , refl 
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt (Ω ++ Λ₁)) [] | ++?-alt-eq₁ (∘cxt Γ) (∘cxt Ω) (∘cxt Λ₁) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (Ω ++ Λ₁)} _)
             (trans (runLeq ℓ)
                    (cong (MMF.runLQ tt ℓ) (trans (only-lf⇑P-at≡ (∘cxt Λ₁) _ _ lf f done)
                                                  (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Λ₁} _) (untag-seq≡ {Γ = ∘cxt Λ₁}{∘cxt Λ₁} _ refl))))))))))
only-rf-f-at-lf-fP {S = S} {Γ = Γ} Γ₀ Γ₁ Γ₂ (focl {Γ₀ = Λ₀} {.(A ∷ Ω ++ map (λ A₁ → ∘ , A₁) Γ₁)} {Q = Q} q lf (focr {_} {_} {_} {_} {_} {_} {[]} (just (M , m)) blurr (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ | inj₂ (A , Ω , eq' , refl) with split-map ∘fma Γ Λ₀ (_ ∷ Ω) eq'
only-rf-f-at-lf-fP {S = S} {Γ = .(Λ₀' ++ A' ∷ Ω')} Γ₀ Γ₁ Γ₂ (focl {Γ₀ = .(map (λ A → ∘ , A) Λ₀')} {.((∘ , A') ∷ map (λ A → ∘ , A) Ω' ++ map _ Γ₁)} {Q = I} q lf (focr {_} {_} {_} {_} {_} {_} {[]} (just (` X , _)) blurr (unfoc (inj₁ p) f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Ω') , eq' , refl) | Λ₀' , A' ∷ Ω' , refl , refl , refl
  rewrite ++?-alt-eq₁ (∘cxt (Λ₀' ++ A' ∷ Ω')) (∘cxt Γ₁) [] | ++?-alt-eq₂ (∘fma A') (∘cxt Λ₀') (∘cxt Ω') (∘cxt Γ₁) | split-map-eq ∘fma Λ₀' (A' ∷ Ω') =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _)
      (trans (runLeq ℓ)
             (cong (MMF.runLQ tt ℓ) (trans (only-lf⇑P-at≡ _ _ _ lf f done)
                                           (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (_ ∷ Ω' ++ Γ₁)} _) (untag-seq≡ {Γ = ∘cxt (_ ∷ Ω' ++ Γ₁)}{∘cxt (_ ∷ Ω' ++ Γ₁)} _ refl))))))))))
only-rf-f-at-lf-fP {S = S} {Γ = .(Λ₀' ++ A' ∷ Ω')} Γ₀ Γ₁ Γ₂ (focl {Γ₀ = .(map (λ A → ∘ , A) Λ₀')} {.((∘ , A') ∷ map (λ A → ∘ , A) Ω' ++ map _ Γ₁)} {Q = _ ⊗ _} q lf (focr {_} {_} {_} {_} {_} {_} {[]} (just (` X , _)) blurr (unfoc (inj₁ p) f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Ω') , eq' , refl) | Λ₀' , A' ∷ Ω' , refl , refl , refl
  rewrite ++?-alt-eq₁ (∘cxt (Λ₀' ++ A' ∷ Ω')) (∘cxt Γ₁) [] | ++?-alt-eq₂ (∘fma A') (∘cxt Λ₀') (∘cxt Ω') (∘cxt Γ₁) | split-map-eq ∘fma Λ₀' (A' ∷ Ω') =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _)
      (trans (runLeq ℓ)
             (cong (MMF.runLQ tt ℓ) (trans (only-lf⇑P-at≡ _ _ _ lf f done)
                                           (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (_ ∷ Ω' ++ Γ₁)} _) (untag-seq≡ {Γ = ∘cxt (_ ∷ Ω' ++ Γ₁)}{∘cxt (_ ∷ Ω' ++ Γ₁)} _ refl))))))))))
only-rf-f-at-lf-fP Γ₀ Γ₁ Γ₂ {x = x} (focl q lf (unfoc ok f) eq₁ eq' ξ) eq ℓ = ⊥-elim (∙r⇑-at x f)
only-rf-f-at-lf-fP Γ₀ Γ₁ Γ₂ {x = x} (focr s (⊗r+ Δ₀ Ξ m₁ rf gs) f eq' eq'' ξ) eq ℓ = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))
only-rf-f-at-lf-fP Γ₀ Γ₁ Γ₂ {X = ` X} (focr {Γ₁ = []} (just _) blurr (unfoc () f) refl refl ξ) refl ℓ

only-rf⇑-lf⇑ : ∀ {S} Γ₀ Γ₁ Γ₂ {M Q R} ok
  {s : isIrr S} {r : isPosAt R} {m : isNegAt M} {q : isPosAt Q}
  {lf : r ⇛lf S ∣ Γ₀}
  {rf : just (M , m) MMF.⇛rf Γ₂ ； Q}
  (f : (∘ , just R) MMF.∣ ∘cxt Γ₁ ⇑ (∘ , M)) → 
  only-rf⇑ (∘cxt (Γ₀ ++ Γ₁)) m q rf (only-lf⇑ (∘cxt Γ₁) s r lf f)
    ≡ foc s q (focl {Γ₀ = ∘cxt Γ₀} r lf (focr {Γ₀ = ∘cxt Γ₁}{∘cxt Γ₂} (just (M , m)) rf (unfoc ok f) refl refl tt) refl refl tt)

only-rf⇑N-lf⇑P : ∀ {S S'} Γ Γ₀ Γ₁ Γ₂ Δ {P Q R}
  {s : isIrr S} {p : isPos P} {n : isNeg (Δ ⊸⋆ R)} {q : isPosAt Q}
  {lf : pos→posat p ⇛lf S ∣ Γ₀}
  {rf : just (Δ ⊸⋆ R , neg→negat n) MMF.⇛rf Γ₂ ； Q}
  (f : (∘ , S') MMF.∣ ∘cxt Γ ++ ∘cxt Γ₁ ++ ∘cxt Δ ⇑ (∘ , R)) → 
  (ℓ : MF.L S' Γ P) →
  only-rf⇑N (∘cxt (Γ₀ ++ Γ₁)) Δ n q rf (only-lf⇑P (∘cxt (Γ₁ ++ Δ)) s p lf f ℓ)  
    ≡ foc s q (focl {Γ₀ = ∘cxt Γ₀} (pos→posat p) lf (focr {Γ₀ = ∘cxt Γ₁} {Γ₁ = ∘cxt Γ₂} (just (Δ ⊸⋆ R , neg→negat n)) rf (unfoc (inj₁ p) (MMF.⊸r⋆⇑ Δ (MMF.runL ℓ f))) refl refl tt) refl refl tt)

only-rf-fN-lf-fP : ∀ {S T Δ'} Γ Γ₀ Γ₁ Γ₂ Δ {P Q R}
  {s : isIrr S} {t : isIrr T} {p : isPos P} {n : isNeg (Δ ⊸⋆ R)} {q : isPosAt Q} {r : isPosAt R}
  {lf : pos→posat p ⇛lf T ∣ Γ₀}
  {rf : just (Δ ⊸⋆ R , neg→negat n) MMF.⇛rf Γ₂ ； Q}
  (f : MMF.[ ∘ , ∘ ] (∘ , S) ∣ Δ' ⇓ (∘ , R))
  (eq : Δ' ≡ ∘cxt Γ ++ ∘cxt Γ₁ ++ ∘cxt Δ) → 
  (ℓ : MF.L S Γ P) →
  only-rf-fN (∘cxt (Γ₀ ++ Γ₁)) Δ t n q r rf (only-lf-fP (∘cxt (Γ₁ ++ Δ)) s p r lf f eq ℓ) refl
    ≡ focl {Γ₀ = ∘cxt Γ₀} (pos→posat p) lf (focr {Γ₀ = ∘cxt Γ₁} {Γ₁ = ∘cxt Γ₂} (just (Δ ⊸⋆ R , neg→negat n)) rf (unfoc (inj₁ p) (MMF.⊸r⋆⇑ Δ (MMF.runLQ r ℓ (foc s r (subst⇓ f eq))))) refl refl tt) refl refl tt

only-rf⇑-lf⇑ Γ₀ Γ₁ Γ₂ {` _} {R = ` x} (inj₂ (_ , ())) f
only-rf⇑-lf⇑ Γ₀ Γ₁ Γ₂ {M ⊸ M₁} {R = ` x} (inj₂ (_ , m)) f = only-rf⇑N-lf⇑-at Γ₀ Γ₁ Γ₂ [] f
only-rf⇑-lf⇑ Γ₀ Γ₁ Γ₂ {` X} {R = I} (inj₁ tt) f = only-rf⇑-at-lf⇑P Γ₀ Γ₁ Γ₂ f done
only-rf⇑-lf⇑ Γ₀ Γ₁ Γ₂ {M ⊸ M₁} {R = I} (inj₁ tt) f = only-rf⇑N-lf⇑P [] Γ₀ Γ₁ Γ₂ [] f done
only-rf⇑-lf⇑ Γ₀ Γ₁ Γ₂ {` X} {R = R ⊗ R₁} (inj₁ tt) f = only-rf⇑-at-lf⇑P Γ₀ Γ₁ Γ₂ f done
only-rf⇑-lf⇑ Γ₀ Γ₁ Γ₂ {M ⊸ M₁} {R = R ⊗ R₁} (inj₁ tt) f = only-rf⇑N-lf⇑P [] Γ₀ Γ₁ Γ₂ [] f done

only-rf⇑N-lf⇑P Γ Γ₀ Γ₁ Γ₂ Δ (⊸r f) ℓ =
  trans (only-rf⇑N-lf⇑P Γ Γ₀ Γ₁ Γ₂ (Δ ∷ʳ _) f ℓ)
        (congfoc (congfocl refl (congfocr refl (cong (unfoc _) (trans (⊸r⋆⊸r⋆⇑ Δ (_ ∷ []) _) (cong (MMF.⊸r⋆⇑ Δ) (⊸r⋆runL (_ ∷ []) ℓ)))))))
only-rf⇑N-lf⇑P Γ Γ₀ Γ₁ Γ₂ Δ (Il q f) ℓ =
  trans (only-rf⇑N-lf⇑P Γ Γ₀ Γ₁ Γ₂ Δ f (Il-1 ℓ))
        (congfoc (congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ Δ) (cong (MMF.runL ℓ) (Il⇑eq _)))))))
only-rf⇑N-lf⇑P Γ Γ₀ Γ₁ Γ₂ Δ (⊗l q f) ℓ =
  trans (only-rf⇑N-lf⇑P (_ ∷ Γ) Γ₀ Γ₁ Γ₂ Δ f (⊗l-1 ℓ))
        (congfoc (congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ Δ) (cong (MMF.runL ℓ) (⊗l⇑eq _)))))))
only-rf⇑N-lf⇑P Γ Γ₀ Γ₁ Γ₂ Δ {q = q} (foc s _ f) ℓ =
  congfoc (trans (only-rf-fN-lf-fP Γ Γ₀ Γ₁ Γ₂ Δ {q = q} f refl ℓ)
                 (congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ Δ) (sym (runLeq ℓ)))))))

only-rf-fN-lf-fP Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₃}{Γ₄} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) eq ℓ with ++?-alt (∘cxt Γ) Γ₃ (∘cxt (Γ₁ ++ Δ)) Γ₄ eq
... | inj₂ (A , Ω , eq' , refl) with split-map ∘fma Γ Γ₃ (A ∷ Ω) eq'
only-rf-fN-lf-fP .(Λ ++ A' ∷ Λ') Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = .(map (λ A → ∘ , A) Λ)} {.((∘ , A') ∷ map (λ A → ∘ , A) Λ' ++ map _ Γ₁ ++ map _ Δ)} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) refl ℓ | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Λ') , refl , refl) | Λ , A' ∷ Λ' , refl , refl , refl 
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt Δ) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (cong (MMF.⊸r⋆⇑ Δ) (r∙→∘⇑-runLQ {Δ = ∘cxt (Γ₁ ++ Δ)} ℓ _))))
only-rf-fN-lf-fP Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = .(map (λ A → ∘ , A) Γ ++ Ω)} {Γ₄} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) eq ℓ | inj₁ (Ω , refl , eq') with split-map++ Ω Γ₄ Γ₁ Δ (sym eq')
only-rf-fN-lf-fP Γ Γ₀ .(Λ ++ Λ') Γ₂ Δ (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Λ)} {.(map (λ z → ∘ , z) Λ' ++ map (λ z → ∘ , z) Δ)} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Λ) , refl , refl) | inj₁ (Λ , Λ' , refl , refl , refl)
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt (Λ ++ Λ')) (∘cxt Δ) | ++?-eq₁ (∘cxt Λ) (∘cxt Λ') (∘cxt Δ) =
    congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ Δ) (only-rf⇑-at-runLQ _ ℓ))))
only-rf-fN-lf-fP Γ Γ₀ Γ₁ Γ₂ .(A ∷ Λ ++ Λ') (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Γ₁ ++ (∘ , A) ∷ map (λ z → ∘ , z) Λ)} {.(map (λ z → ∘ , z) Λ')} q lf (focr (just (` X , _)) rf ax refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Γ₁ ++ (∘ , A) ∷ map (λ z → ∘ , z) Λ) , refl , refl) | inj₂ (A , Λ , Λ' , refl , refl , refl)
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt (A ∷ Λ ++ Λ')) | ++?-eq₂ (∘fma A) (∘cxt Γ₁) (∘cxt Λ) (∘cxt Λ') | split-map-eq ∘fma Λ Λ' =
    congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ (_ ∷ Λ ++ Λ')) (only-rf⇑-at-runLQ _ ℓ))))

only-rf-fN-lf-fP Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₅} q lf (focr {Γ₀ = Γ₃}{Γ₄} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ with ++?-alt (∘cxt Γ) (Γ₅ ++ Γ₃) (∘cxt (Γ₁ ++ Δ)) Γ₄ eq
... | inj₂ (A , Ω , eq' , refl) with split-map ∘fma Γ Γ₅ (Γ₃ ++ A ∷ Ω) eq'
... | Ξ , Ξ' , refl , eq₀ , refl with split-map ∘fma Ξ' Γ₃ (_ ∷ Ω) eq₀
only-rf-fN-lf-fP .(Ξ ++ Γ₃' ++ A' ∷ Ω') Γ₀ Γ₁ Γ₂ Δ (focl {_} {_} {_} {_} {.(map _ Ξ)} q lf (focr {Γ₀ = .(map (λ A → ∘ , A) Γ₃')} {.((∘ , A') ∷ map (λ A → ∘ , A) Ω' ++ map _ Γ₁ ++ map _ Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Ω') , eq' , refl) | Ξ , .(Γ₃' ++ A' ∷ Ω') , refl , eq₀ , refl | Γ₃' , A' ∷ Ω' , refl , refl , refl
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt Δ) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (cong (MMF.⊸r⋆⇑ Δ) (r∙→∘⇑-runLQ {Δ = ∘cxt (Γ₁ ++ Δ)} ℓ _))))
only-rf-fN-lf-fP Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₅} q lf (focr {Γ₀ = Γ₃}{Γ₄} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ | inj₁ (Ω , eq' , eq'') with ++?-alt (∘cxt Γ) Γ₅ Ω Γ₃ eq'
... | inj₂ (A , Ω , eq₀ , refl) with split-map ∘fma Γ Γ₅ (_ ∷ Ω) eq₀
only-rf-fN-lf-fP .(Γ₅' ++ A' ∷ Ω') Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₅')} q lf (focr {_} {_} {_} {_} {_} {.((∘ , A') ∷ map (λ A → ∘ , A) Ω' ++ Ω)} {Γ₄} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ | inj₁ (Ω , refl , eq'') | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Ω') , eq₀ , refl) | Γ₅' , A' ∷ Ω' , refl , refl , refl with split-map++ Ω Γ₄ Γ₁ Δ (sym eq'')
only-rf-fN-lf-fP .(Γ₅' ++ A' ∷ Ω') Γ₀ .(Ξ ++ Ξ') Γ₂ Δ {r = r} (focl {_} {_} {_} {_} {.(map _ Γ₅')} q lf (focr {_} {_} {_} {_} {_} {.((∘ , A') ∷ map _ Ω' ++ map (λ z → ∘ , z) Ξ)} {.(map (λ z → ∘ , z) Ξ' ++ map (λ z → ∘ , z) Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Ξ) , refl , refl) | inj₂ (.(∘ , A') , .(map _ Ω') , eq₀ , refl) | Γ₅' , A' ∷ Ω' , refl , refl , refl | inj₁ (Ξ , Ξ' , refl , refl , refl)
  rewrite ++?-alt-eq₂ (∘fma A') (∘cxt Γ₅') (∘cxt Ω') (∘cxt Ξ) | split-map-eq ∘fma Γ₅' (A' ∷ Ω') | ++?-eq₁ (∘cxt Γ₀) (∘cxt (Ξ ++ Ξ')) (∘cxt Δ) | ++?-eq₁ (∘cxt Ξ) (∘cxt Ξ') (∘cxt Δ) =
    congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ Δ)
      (trans (only-rf⇑-runL (only-lf⇑ (∘cxt (A' ∷ Ω' ++ Ξ)) _ q lf f) ℓ)
             (cong (MMF.runLQ r ℓ) (only-rf⇑-lf⇑ Γ₅' (_ ∷ Ω' ++ Ξ) (Ξ' ++ Δ) ok f))))))  
only-rf-fN-lf-fP .(Γ₅' ++ A' ∷ Ω') Γ₀ Γ₁ Γ₂ .(A'' ∷ Ξ ++ Ξ') {s = s} {r = r} (focl {_} {_} {_} {_} {.(map _ Γ₅')} q lf (focr {_} {_} {_} {_} {_} {.((∘ , A') ∷ map _ Ω' ++ map (λ z → ∘ , z) Γ₁ ++ (∘ , A'') ∷ map (λ z → ∘ , z) Ξ)} {.(map (λ z → ∘ , z) Ξ')} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Γ₁ ++ (∘ , A'') ∷ map (λ z → ∘ , z) Ξ) , refl , refl) | inj₂ (.(∘ , A') , .(map _ Ω') , eq₀ , refl) | Γ₅' , A' ∷ Ω' , refl , refl , refl | inj₂ (A'' , Ξ , Ξ' , refl , refl , refl)
  rewrite ++?-alt-eq₂ (∘fma A') (∘cxt Γ₅') (∘cxt Ω') (∘cxt (Γ₁ ++ A'' ∷ Ξ)) | split-map-eq ∘fma Γ₅' (A' ∷ Ω') | ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt (A'' ∷ Ξ ++ Ξ')) | ++?-eq₂ (∘fma A'') (∘cxt Γ₁) (∘cxt Ξ) (∘cxt Ξ') | split-map-eq ∘fma Ξ Ξ' = 
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (cong (MMF.⊸r⋆⇑ (_ ∷ Ξ ++ Ξ'))
      (trans (only-rf⇑-runL {Δ₀ = ∘cxt (Γ₁ ++ A'' ∷ Ξ)} (only-lf⇑ (∘cxt (A' ∷ Ω' ++ Γ₁ ++ A'' ∷ Ξ)) _ q lf f) ℓ)
             (cong (MMF.runLQ r ℓ) (only-rf⇑-lf⇑ Γ₅' (A' ∷ Ω' ++ Γ₁ ++ A'' ∷ Ξ) Ξ' ok f))))))
only-rf-fN-lf-fP Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = .(map (λ A → ∘ , A) Γ ++ Λ)} q lf (focr {Γ₀ = Γ₃} {Γ₄} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) eq ℓ | inj₁ (.(Λ ++ Γ₃) , refl , eq'') | inj₁ (Λ , refl , refl) with split-map++₂ Λ Γ₃ Γ₄ Γ₁ Δ (sym eq'')
only-rf-fN-lf-fP Γ Γ₀ .(Ξ ++ Ξ' ++ Ξ'') Γ₂ Δ {r = r} (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Ξ)} q lf (focr {Γ₀ = .(map (λ z → ∘ , z) Ξ')} {.(map (λ z → ∘ , z) Ξ'' ++ map (λ z → ∘ , z) Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Ξ ++ map (λ z → ∘ , z) Ξ') , refl , refl) | inj₁ (.(map (λ z → ∘ , z) Ξ) , refl , refl) | inj₁ (Ξ , Ξ' , Ξ'' , refl , refl , refl , refl)
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt Ξ) (∘cxt Ξ') | ++?-eq₁ (∘cxt Γ₀) (∘cxt (Ξ ++ Ξ' ++ Ξ'')) (∘cxt Δ) | ++?-eq₁ (∘cxt (Ξ ++ Ξ')) (∘cxt Ξ'') (∘cxt Δ) =
    congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ Δ)
      (trans (only-rf⇑-runL (only-lf⇑ (∘cxt Ξ') _ q lf f) ℓ) 
             (cong (MMF.runLQ r ℓ) (only-rf⇑-lf⇑ (Γ ++ Ξ) Ξ' (Ξ'' ++ Δ) ok f))))))
only-rf-fN-lf-fP Γ Γ₀ .(Ξ ++ Ξ') Γ₂ .(A' ∷ Ξ'' ++ Ξ''') {s = s} {r = r} (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Ξ)} q lf (focr {Γ₀ = .(map (λ z → ∘ , z) Ξ' ++ (∘ , A') ∷ map (λ z → ∘ , z) Ξ'')} {.(map (λ z → ∘ , z) Ξ''')} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Ξ ++ map (λ z → ∘ , z) Ξ' ++ (∘ , A') ∷ map (λ z → ∘ , z) Ξ'') , refl , refl) | inj₁ (.(map (λ z → ∘ , z) Ξ) , refl , refl) | inj₂ (inj₁ (Ξ , Ξ' , A' , Ξ'' , Ξ''' , refl , refl , refl , refl , refl))
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt Ξ) (∘cxt (Ξ' ++ A' ∷ Ξ'')) | ++?-eq₁ (∘cxt Γ₀) (∘cxt (Ξ ++ Ξ')) (∘cxt (A' ∷ Ξ'' ++ Ξ''')) | ++?-eq₂ (∘fma A') (∘cxt (Ξ ++ Ξ')) (∘cxt Ξ'') (∘cxt Ξ''') | split-map-eq ∘fma Ξ'' Ξ''' =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (Ξ ++ Ξ')} _) (cong (MMF.⊸r⋆⇑ {Γ = ∘cxt (Ξ ++ Ξ')} (_ ∷ Ξ'' ++ Ξ'''))
      (trans (only-rf⇑-runL {Δ₀ = ∘cxt (Ξ ++ Ξ' ++ _ ∷ Ξ'')}{Ξ'''} (only-lf⇑ {Δ₀ = Γ ++ Ξ} (∘cxt (Ξ' ++ A' ∷ Ξ'')) s q lf f) ℓ)
             (cong (MMF.runLQ r ℓ) (only-rf⇑-lf⇑ (Γ ++ Ξ) (Ξ' ++ _ ∷ Ξ'') Ξ''' ok f))))))
only-rf-fN-lf-fP Γ Γ₀ Γ₁ Γ₂ .(A' ∷ Ξ ++ Ξ' ++ Ξ'') {r = r} (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Γ₁ ++ (∘ , A') ∷ map (λ z → ∘ , z) Ξ)} q lf (focr {Γ₀ = .(map (λ z → ∘ , z) Ξ')} {.(map (λ z → ∘ , z) Ξ'')} (just (M , m)) rf (unfoc ok f) refl refl ξ₁) refl refl ξ) refl ℓ | inj₁ (.((map (λ z → ∘ , z) Γ₁ ++ (∘ , A') ∷ map (λ z → ∘ , z) Ξ) ++ map (λ z → ∘ , z) Ξ') , refl , refl) | inj₁ (.(map (λ z → ∘ , z) Γ₁ ++ (∘ , A') ∷ map (λ z → ∘ , z) Ξ) , refl , refl) | inj₂ (inj₂ (A' , Ξ , Ξ' , Ξ'' , refl , refl , refl , refl))
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt (Γ₁ ++ A' ∷ Ξ)) (∘cxt Ξ') | ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt (A' ∷ Ξ ++ Ξ' ++ Ξ'')) | ++?-eq₂ (∘fma A') (∘cxt Γ₁) (∘cxt (Ξ ++ Ξ')) (∘cxt Ξ'') | split-map-eq ∘fma (Ξ ++ Ξ') Ξ'' =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (cong (MMF.⊸r⋆⇑ (_ ∷ Ξ ++ Ξ' ++ Ξ''))
      (trans (only-rf⇑-runL {Δ₀ = ∘cxt (Γ₁ ++ A' ∷ Ξ ++ Ξ')} (only-lf⇑ (∘cxt Ξ') _ q lf f) ℓ) 
             (cong (MMF.runLQ r ℓ) (only-rf⇑-lf⇑ (Γ ++ Γ₁ ++ _ ∷ Ξ) Ξ' Ξ'' ok f)))))) 

only-rf-fN-lf-fP Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₃}{Γ₄} q lf (unfoc ok f) refl refl ξ) eq ℓ with ++?-alt (∘cxt Γ) Γ₃ (∘cxt (Γ₁ ++ Δ)) Γ₄ eq
... | inj₁ (Λ , refl , eq') with split-map++ Λ Γ₄ Γ₁ Δ (sym eq')
only-rf-fN-lf-fP Γ Γ₀ .(Ω ++ Ω') Γ₂ Δ {s = s}{r = r} (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Ω)} {.(map (λ z → ∘ , z) Ω' ++ map (λ z → ∘ , z) Δ)} q lf (unfoc ok f) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Ω) , refl , refl) | inj₁ (Ω , Ω' , refl , refl , refl)
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt (Ω ++ Ω')) (∘cxt Δ) | r∙→∘⇑-runLQ {Γ = Γ}{∘cxt (Ω ++ Ω' ++ Δ)} {q = r} ℓ (foc s r (focl {Γ₀ = ∙cxt Γ ++ ∘cxt Ω}{∘cxt (Ω' ++ Δ)} q lf (unfoc ok f) refl refl tt)) = refl
only-rf-fN-lf-fP Γ Γ₀ Γ₁ Γ₂ .(A' ∷ Ω ++ Ω') (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Γ₁ ++ (∘ , A') ∷ map (λ z → ∘ , z) Ω)} {.(map (λ z → ∘ , z) Ω')} q lf (unfoc ok f) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Γ₁ ++ (∘ , A') ∷ map (λ z → ∘ , z) Ω) , refl , refl) | inj₂ (A' , Ω , Ω' , refl , refl , refl)
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt (A' ∷ Ω ++ Ω')) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (cong (MMF.⊸r⋆⇑ (_ ∷ Ω ++ Ω')) (r∙→∘⇑-runLQ {Δ = ∘cxt (Γ₁ ++ A' ∷ Ω ++ Ω')} ℓ _))))
only-rf-fN-lf-fP Γ Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = Γ₃} {.(A ∷ Λ ++ map (λ z → ∘ , z) Γ₁ ++ map (λ z → ∘ , z) Δ)} q lf (unfoc ok f) refl refl ξ) eq ℓ | inj₂ (A , Λ , eq' , refl) with split-map ∘fma Γ Γ₃ (_ ∷ Λ) eq'
only-rf-fN-lf-fP .(Γ₃' ++ A' ∷ Λ') Γ₀ Γ₁ Γ₂ Δ (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₃')} {.((∘ , A') ∷ map (λ A → ∘ , A) Λ' ++ map _ Γ₁ ++ map _ Δ)} q lf (unfoc ok f) refl refl ξ) refl ℓ | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Λ') , refl , refl) | Γ₃' , A' ∷ Λ' , refl , refl , refl
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt Δ) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁}_) (cong (MMF.⊸r⋆⇑ Δ) (r∙→∘⇑-runLQ {Δ = ∘cxt (Γ₁ ++ Δ)} ℓ _))))

only-rf-fN-lf-fP Γ Γ₀ Γ₁ Γ₂ Δ (focr {Γ₀ = Γ₃} {Γ₄} (just (M , m)) rf (unfoc ok f) refl refl ξ) eq ℓ with ++?-alt (∘cxt Γ) Γ₃ (∘cxt (Γ₁ ++ Δ)) Γ₄ eq
... | inj₁ (Λ , refl , eq') with split-map++ Λ Γ₄ Γ₁ Δ (sym eq')
only-rf-fN-lf-fP Γ Γ₀ .(Ω ++ Ω') Γ₂ Δ (focr {_} {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Ω)} {.(map (λ z → ∘ , z) Ω' ++ map (λ z → ∘ , z) Δ)} (just (M ⊸ M' , m)) rf (unfoc ok f) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Ω) , refl , refl) | inj₁ (Ω , Ω' , refl , refl , refl)
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt (Ω ++ Ω')) (∘cxt Δ) | ++?-eq₁ (∘cxt Ω) (∘cxt Ω') (∘cxt Δ) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt (Ω ++ Ω')} _) (cong (MMF.⊸r⋆⇑ {Γ = ∘cxt (Ω ++ Ω')} Δ)
      (trans (only-rf⇑-runL (l∙→∘⇑ f) ℓ) 
             (cong (MMF.runLQ _ ℓ) (only-rf⇑N-l∙ {Δ₀ = Γ ++ Ω}{Ω' ++ Δ}{[]} f))))))
only-rf-fN-lf-fP Γ Γ₀ Γ₁ Γ₂ .(A ∷ Ω ++ Ω') (focr {_} {_} {_} {_} {_} {.(map _ Γ ++ map (λ z → ∘ , z) Γ₁ ++ (∘ , A) ∷ map (λ z → ∘ , z) Ω)} {.(map (λ z → ∘ , z) Ω')} (just (M ⊸ M' , m)) rf (unfoc ok f) refl refl ξ) refl ℓ | inj₁ (.(map (λ z → ∘ , z) Γ₁ ++ (∘ , A) ∷ map (λ z → ∘ , z) Ω) , refl , refl) | inj₂ (A , Ω , Ω' , refl , refl , refl)
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt (A ∷ Ω ++ Ω')) | ++?-eq₂ (∘fma A) (∘cxt Γ₁) (∘cxt Ω) (∘cxt Ω') | split-map-eq ∘fma Ω Ω' =
    congfocl refl (congfocr refl (cong (unfoc _) (cong (MMF.⊸r⋆⇑ (_ ∷ Ω ++ Ω'))
      (trans (only-rf⇑-runL (l∙→∘⇑ f)  ℓ)
             (cong (MMF.runLQ _ ℓ) (only-rf⇑N-l∙ {Δ₀ = Γ ++ Γ₁ ++ A ∷ Ω}{Ω'}{[]} f))))))
only-rf-fN-lf-fP Γ Γ₀ Γ₁ Γ₂ Δ (focr {Γ₀ = Γ₃} {.(A ∷ Λ ++ map (λ z → ∘ , z) Γ₁ ++ map (λ z → ∘ , z) Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ) eq ℓ | inj₂ (A , Λ , eq' , refl) with split-map ∘fma Γ Γ₃ (A ∷ Λ) eq'
only-rf-fN-lf-fP .(Γ₃' ++ A' ∷ Λ') Γ₀ Γ₁ Γ₂ Δ (focr {Γ₀ = .(map (λ A → ∘ , A) Γ₃')} {.((∘ , A') ∷ map (λ A → ∘ , A) Λ' ++ map _ Γ₁ ++ map _ Δ)} (just (M , m)) rf (unfoc ok f) refl refl ξ) refl ℓ | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Λ') , refl , refl) | Γ₃' , A' ∷ Λ' , refl , refl , refl
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt Δ) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (cong (MMF.⊸r⋆⇑ Δ) (r∙→∘⇑-runLQ {Δ = ∘cxt (Γ₁ ++ Δ)} ℓ _))))
only-rf-fN-lf-fP Γ Γ₀ Γ₁ Γ₂ Δ (focr ─ rf (refl , refl) refl refl ξ) refl ℓ
  rewrite ++?-eq₁ (∘cxt Γ₀) (∘cxt Γ₁) (∘cxt Δ) =
    congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₁} _) (cong (MMF.⊸r⋆⇑ Δ) (r∙→∘⇑-runLQ {Δ = ∘cxt (Γ₁ ++ Δ)} ℓ _))))

only-rf⇑eq : ∀ {S Δ₀ Δ₁ N Q} (n : isNeg N) {q : isPosAt Q}
              {rf : just (N , neg→negat n) MMF.⇛rf Δ₁ ； Q}
               (f : (∘ , S) MMF.∣ Δ₀ ⇑ (∘ , N)) → 
              ------------------------------------
               only-rf⇑ Δ₀ (neg→negat n) q rf f ≡ only-rf⇑N Δ₀ [] n q rf f 
only-rf⇑eq {N = _ ⊸ _} n f = refl

only-lf⇑≡ : {S : Stp} {Δ₀ : Cxt} {Δ₁ : TCxt} {C P : Fma}
            {s : isIrr S} {p : isPos P} 
            {lf : pos→posat p ⇛lf S ∣ Δ₀}
            (f : (∘ , just P) MMF.∣ Δ₁ ⇑ (∘ , C)) → 
      ------------------------------------
           only-lf⇑ Δ₁ s _ lf f ≡ only-lf⇑P Δ₁ s p lf f done
only-lf⇑≡ {P = I} f = refl
only-lf⇑≡ {P = P ⊗ P₁} f = refl

rtag-∘cxt : {A : _} (Γ : Cxt) → rtag (just A) (∘cxt Γ) ∙ → ⊥
rtag-∘cxt (A ∷ Γ) ξ = rtag-∘cxt Γ ξ


only-lf⇑P-r∙ : {S S' : Stp} {Δ₀ : Cxt} {Δ₁ : Cxt} {Γ : Cxt} {Q P : Fma}
               {s : isIrr S} {p : isPos P} {q : isPosAt Q}
               {lf : pos→posat p ⇛lf S ∣ Δ₀}
               (f : (∘ , S') MMF.∣ ∙cxt Γ ++ ∘cxt Δ₁ ⇑ (∙ , Q)) → 
               (ℓ : MF.L S' Γ P) →
          only-lf⇑P (∘cxt Δ₁) s p lf (r∙→∘⇑ {Γ = ∙cxt Γ ++ ∘cxt Δ₁} f) ℓ
            ≡ foc s q (focl {Γ₀ = ∘cxt Δ₀} {∘cxt Δ₁} _ lf (unfoc p (MMF.runL ℓ f)) refl refl tt)

only-lf⇑P-r∙ {Δ₁ = Δ₁} {p = p} (Il q f) ℓ =
  trans (only-lf⇑P-r∙ f (Il-1 ℓ))
        (congfoc (congfocl refl (cong (unfoc {Γ = ∘cxt Δ₁} p) (cong (MMF.runL ℓ) (Il⇑eq f)))))
only-lf⇑P-r∙ {Δ₁ = Δ₁} {p = p} (⊗l q f) ℓ =
  trans (only-lf⇑P-r∙ f (⊗l-1 ℓ))
        (congfoc (congfocl refl (cong (unfoc {Γ = ∘cxt Δ₁} p) (cong (MMF.runL ℓ) (⊗l⇑eq f)))))
only-lf⇑P-r∙ {Δ₁ = Δ₁} {Γ} (foc s q (focl {Γ₀ = Γ₀} {Γ₁} q₁ lf (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) eq refl ξ)) ℓ with ++? Γ₀ (∙cxt Γ) Γ₁ (∘cxt Δ₁) eq
... | inj₁ (Λ , eq' , refl) with split-map ∘fma Δ₁ Λ Γ₁ eq'
only-lf⇑P-r∙ {Δ₁ = .(Γ₀' ++ Λ')} {Γ} (foc s q (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ A → ∘ , A) Γ₀')} {.(map (λ A → ∘ , A) Λ')} q₁ lf (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) refl refl ξ)) ℓ | inj₁ (.(map (λ A → ∘ , A) Γ₀') , refl , refl) | Γ₀' , Λ' , refl , refl , refl
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt Γ₀') (∘cxt Λ') = ⊥-elim (rtag-∘cxt Λ' ξ₁)
only-lf⇑P-r∙ {Δ₁ = Δ₁} {Γ} (foc s q (focl {Γ₀ = Γ₀} {.(A ∷ Λ ++ map (λ A₁ → ∘ , A₁) Δ₁)} q₁ lf (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) eq refl ξ)) ℓ | inj₂ (A , Λ , eq' , refl) with split-map ∙fma Γ Γ₀ (A ∷ Λ) eq'
only-lf⇑P-r∙ {Δ₁ = Δ₁} {.(Γ₀' ++ A' ∷ Λ')} {p = p} {q = q₂}(foc s q (focl {Γ₀ = .(map (λ A → ∙ , A) Γ₀')} {.((∙ , A') ∷ map (λ A → ∙ , A) Λ' ++ map _ Δ₁)} q₁ lf (focr (just (.(` _) , snd)) rf ax refl refl ξ₁) refl refl ξ)) ℓ | inj₂ (.(∙ , A') , .(map (λ A → ∙ , A) Λ') , refl , refl) | Γ₀' , A' ∷ Λ' , refl , refl , refl 
  rewrite ++?-alt-eq₂ (∘fma A') (∘cxt Γ₀')  (∘cxt Λ') (∘cxt Δ₁) |
          split-map-eq ∘fma Γ₀' (A' ∷ Λ') | isProp-isPosAt q q₂ =
  congfoc (congfocl refl (cong (unfoc p) (sym (runLeq ℓ))))
only-lf⇑P-r∙ {Δ₁ = Δ₁} {Γ} (foc s q (focl {Γ₀ = Γ₂} q₁ lf (focr {Γ₀ = Γ₀} {Γ₁} (just x) rf (unfoc ok f) refl refl ξ₁) eq refl ξ)) ℓ with ++? (Γ₂ ++ Γ₀) (∙cxt Γ) Γ₁ (∘cxt Δ₁) eq
... | inj₁ (Λ , eq' , eq'') with split-map ∘fma Δ₁ Λ Γ₁ eq'
... | (Γ₀' , Λ' , refl , refl , refl) = ⊥-elim (rtag-∘cxt Λ' ξ₁)
only-lf⇑P-r∙ {S} {Δ₁ = Δ₁} {Γ} (foc s q (focl {Γ₀ = Γ₂} q₁ lf (focr {Γ₀ = Γ₀} {.(A ∷ Λ ++ map (λ A₁ → ∘ , A₁) Δ₁)} (just x) rf (unfoc ok f) refl refl ξ₁) eq refl ξ)) ℓ | inj₂ (A , Λ , eq' , refl) with split-map ∙fma Γ (Γ₂ ++ Γ₀) (A ∷ Λ) eq'
... | Ω , A' ∷ Λ' , eq'' , refl , refl with split-map ∙fma Ω Γ₂ Γ₀ eq''
only-lf⇑P-r∙ {S} {Δ₁ = Δ₁} {.((Γ₂' ++ Γ₀') ++ A' ∷ Λ')} {p = p} {q = q₂} (foc s q (focl {Γ₀ = .(map (λ A → ∙ , A) Γ₂')} q₁ lf (focr {Γ₀ = .(map (λ A → ∙ , A) Γ₀')} {.((∙ , A') ∷ map _ Λ' ++ map _ Δ₁)} (just x) rf (unfoc ok f) refl refl ξ₁) refl refl ξ)) ℓ | inj₂ (.(∙ , A') , .(map _ Λ') , refl , refl) | .(Γ₂' ++ Γ₀') , A' ∷ Λ' , refl , refl , refl | Γ₂' , Γ₀' , refl , refl , refl
  rewrite ++?-alt-eq₂ (∘fma A') (∘cxt (Γ₂' ++ Γ₀')) (∘cxt Λ') (∘cxt Δ₁) |
          split-map-eq ∘fma Γ₂' (Γ₀' ++ A' ∷ Λ') |
          split-map-eq ∘fma Γ₀' (A' ∷ Λ') | isProp-isPosAt q q₂ =
  congfoc (congfocl refl (cong (unfoc p) (sym (runLeq ℓ))))
only-lf⇑P-r∙ {Δ₁ = Δ₁} {Γ} (foc s q (focl {Γ₀ = Γ₀} {Γ₁} q₁ lf (unfoc ok f) eq refl ξ)) ℓ with ++? Γ₀ (∙cxt Γ) Γ₁ (∘cxt Δ₁) eq
... | inj₁ (Λ , eq' , refl) with split-map ∘fma Δ₁ Λ Γ₁ eq'
only-lf⇑P-r∙ {Δ₁ = .(Γ₀' ++ Λ')} {Γ} {p = p} {q = q₂} (foc s q (focl {_} {_} {_} {_} {.(map _ Γ ++ map (λ A → ∘ , A) Γ₀')} {.(map (λ A → ∘ , A) Λ')} q₁ lf (unfoc ok f) refl refl ξ)) ℓ | inj₁ (.(map (λ A → ∘ , A) Γ₀') , refl , refl) | Γ₀' , Λ' , refl , refl , refl
  rewrite ++?-alt-eq₁ (∘cxt Γ) (∘cxt Γ₀') (∘cxt Λ') | isProp-isPosAt q q₂ =
  congfoc (congfocl refl (cong (unfoc p) (sym (runLeq ℓ))))
only-lf⇑P-r∙ {S} {Δ₁ = Δ₁} {Γ} {p = p} {q = q₂} (foc s q (focl {Γ₀ = Γ₀} {.(A ∷ Λ ++ map (λ A₁ → ∘ , A₁) Δ₁)} q₁ lf (unfoc ok f) eq refl ξ)) ℓ | inj₂ (A , Λ , eq' , refl) with split-map ∙fma Γ Γ₀ (A ∷ Λ) eq'
only-lf⇑P-r∙ {S} {Δ₁ = Δ₁} {.(Γ₀' ++ A' ∷ Λ')} {p = p} {q = q₂} (foc s q (focl {Γ₀ = .(map (λ A → ∙ , A) Γ₀')} {.((∙ , A') ∷ map (λ A → ∙ , A) Λ' ++ map _ Δ₁)} q₁ lf (unfoc ok f) refl refl ξ)) ℓ | inj₂ (.(∙ , A') , .(map (λ A → ∙ , A) Λ') , refl , refl) | Γ₀' , A' ∷ Λ' , refl , refl , refl
  rewrite ++?-alt-eq₂ (∘fma A') (∘cxt Γ₀') (∘cxt Λ') (∘cxt Δ₁) |
          split-map-eq ∘fma Γ₀' (A' ∷ Λ') | isProp-isPosAt q q₂ =
  congfoc (congfocl refl (cong (unfoc p) (sym (runLeq ℓ))))
only-lf⇑P-r∙ {Δ₁ = Δ₁} {Γ} (foc s q (focr {Γ₀ = Γ₀} {Γ₁} (just x) rf (unfoc ok f) eq refl ξ)) ℓ with ++? Γ₀ (∙cxt Γ) Γ₁ (∘cxt Δ₁) eq
... | inj₁ (Λ , eq' , refl) with split-map ∘fma Δ₁ Λ Γ₁ eq'
... | Γ₀' , Λ' , refl , refl , refl = ⊥-elim (rtag-∘cxt Λ' ξ)
only-lf⇑P-r∙ {S} {Δ₁ = Δ₁} {Γ} (foc s q (focr {Γ₀ = Γ₀} {.(A ∷ Λ ++ map (λ A₁ → ∘ , A₁) Δ₁)} (just x) rf (unfoc ok f) eq refl ξ)) ℓ | inj₂ (A , Λ , eq' , refl) with split-map ∙fma Γ Γ₀ (A ∷ Λ) eq'
only-lf⇑P-r∙ {S} {Δ₁ = Δ₁} {.(Γ₀' ++ A' ∷ Λ')} {p = p}{q = q₂} (foc s q (focr {Γ₀ = .(map (λ A → ∙ , A) Γ₀')} {.((∙ , A') ∷ map (λ A → ∙ , A) Λ' ++ map _ Δ₁)} (just x) rf (unfoc ok f) refl refl ξ)) ℓ | inj₂ (.(∙ , A') , .(map (λ A → ∙ , A) Λ') , refl , refl) | Γ₀' , A' ∷ Λ' , refl , refl , refl
  rewrite ++?-alt-eq₂ (∘fma A') (∘cxt Γ₀') (∘cxt Λ') (∘cxt Δ₁) |
          split-map-eq ∘fma Γ₀' (A' ∷ Λ') | isProp-isPosAt q q₂ =
  congfoc (congfocl refl (cong (unfoc p) (sym (runLeq ℓ))))
only-lf⇑P-r∙ {p = p} {q = q₂} (foc s q (focr ─ rf (refl , refl) refl refl ξ)) ℓ
  rewrite isProp-isPosAt q q₂ = congfoc (congfocl refl (cong (unfoc p) (sym (runLeq ℓ))))
