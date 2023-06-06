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

untag-r∙→∘⇑ : ∀ {S Γ C} (f : (∘ , S) MMF.∣ Γ ⇑ (∙ , C))
  → untag⇑ (r∙→∘⇑ f) ≡ untag⇑ f
untag-r∙→∘⇑ (Il q f) = cong (Il q) (untag-r∙→∘⇑ f)
untag-r∙→∘⇑ (⊗l q f) = cong (⊗l q) (untag-r∙→∘⇑ f)
untag-r∙→∘⇑ (foc s q (focl q₁ lf (focr (just x) rf f refl refl ξ₁) refl refl ξ)) =
  cong (foc s q) (cong (λ y → focl q₁ (untag-lf lf) (focr (just x) (untag-rf rf) y refl) refl) (untag-untag-seq-f f))
untag-r∙→∘⇑ (foc s q (focl q₁ lf (unfoc ok f) refl refl ξ)) = refl
untag-r∙→∘⇑ (foc s q (focr (just x) rf f refl refl ξ)) =
  cong (foc s q) (cong (λ y → focr (just x) (untag-rf rf) y refl) (untag-untag-seq-f f))
untag-r∙→∘⇑ (foc s q (focr ─ rf (refl , refl) refl refl ξ)) = refl

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

untag-⊸r⋆⇑ : {l : Tag} {S : Stp} {Γ : TCxt} (Δ : Cxt) {A : Fma}
      (f : (l , S) MMF.∣ Γ ++ tag-cxt l Δ ⇑ (∘ , A)) →
      untag⇑ (MMF.⊸r⋆⇑ Δ f) ≡ MF.⊸r⋆⇑ Δ (untag⇑ {Γ = Γ ++ tag-cxt l Δ} f)
untag-⊸r⋆⇑ [] f = refl
untag-⊸r⋆⇑ {Γ = Γ} (A ∷ Δ) f = cong ⊸r (untag-⊸r⋆⇑ {Γ = Γ ∷ʳ _} Δ f)

MF-only-rfN : {S : Stp} (Δ₀ : Cxt) {Δ₁ : Cxt} (Γ : Cxt) {B Q : Fma}
              (n : isNeg (Γ ⊸⋆ B)) (q : isPosAt Q)
              (rf : just (Γ ⊸⋆ B , neg→negat n) MF.⇛rf Δ₁ ； Q) 
              (f : S MF.∣ Δ₀ ++ Γ ⇑ B) → 
              S MF.∣ Δ₀ ++ Δ₁ ⇑ Q
MF-only-rfN Δ₀ Γ n q rf (⊸r f) = MF-only-rfN Δ₀ (Γ ∷ʳ _) n q rf f
MF-only-rfN Δ₀ Γ n q rf (Il q₁ f) = Il q (MF-only-rfN Δ₀ Γ n q rf f)
MF-only-rfN Δ₀ Γ n q rf (⊗l q₁ f) = ⊗l q (MF-only-rfN (_ ∷ Δ₀) Γ n q rf f)
MF-only-rfN Δ₀ Γ n q rf (foc s q₁ f) = foc s q (focr _ rf (unfoc n (MF.⊸r⋆⇑ Γ (foc s q₁ f))) refl)

MF-only-rfN-eq : {S : Stp} (Δ₀ : Cxt) {Δ₁ : Cxt} (Γ : Cxt) {B Q : Fma}
                 (s : isIrr S) (n : isNeg (Γ ⊸⋆ B)) (q : isPosAt Q)
                 (rf : just (Γ ⊸⋆ B , neg→negat n) MF.⇛rf Δ₁ ； Q) 
                 (f : S MF.∣ Δ₀ ++ Γ ⇑ B) → 
                 MF-only-rfN Δ₀ Γ n q rf f ≡ foc s q (focr _ rf (unfoc n (MF.⊸r⋆⇑ Γ f)) refl)
MF-only-rfN-eq Δ₀ Γ s n q rf (⊸r f) =
  trans (MF-only-rfN-eq Δ₀ (Γ ∷ʳ _) s n q rf f)
        (cong (foc s q) (cong (λ x →  focr (just (Γ ⊸⋆ _ , neg→negat n)) rf (unfoc n x) refl) (EqC.⊸r⋆⊸r⋆⇑ Γ {_ ∷ []})))
MF-only-rfN-eq {S} Δ₀ Γ s n q rf (foc s₁ q₁ f)
  rewrite isProp-isIrr {S} s s₁ = refl

MF-only-rf-at : {S : Stp} (Δ₀ : TCxt) {Δ₁ : Cxt} {X Q : Fma}
                (x : isAt X) (q : isPosAt Q)
                (rf : just (X , at→negat x) MF.⇛rf Δ₁ ； Q) 
                (f : (∘ , S) MMF.∣ Δ₀ ⇑ (∘ , X)) → S MF.∣ untag-cxt Δ₀ ++ Δ₁ ⇑ Q
MF-only-rf-at Δ₀ x q rf (Il q₁ f) = Il q (MF-only-rf-at Δ₀ x q rf f)
MF-only-rf-at Δ₀ x q rf (⊗l q₁ f) = ⊗l q (MF-only-rf-at (_ ∷ Δ₀) x q rf f)
MF-only-rf-at _ x q rf (foc s q₁ (focl q₂ lf (focr s₁ (⊗r+ Δ₀ Ξ m rf₁ gs) f eq eq' ξ₁) refl refl ξ)) =
  ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (map proj₂ Ξ)) (at→negat x))
MF-only-rf-at _ {Δ₁} x q rf (foc s q₁ (focl {Γ₁ = Γ₁} q₂ lf (focr {Γ₁ = []} ._ blurr f refl refl ξ₁) refl refl ξ)) =
  foc s q (focl q₂ (untag-lf lf) (focr {Γ₀ = untag-cxt Γ₁} _ rf (untag⇓ f) refl) refl)
MF-only-rf-at _ x q rf (foc s q₁ (focl {Γ₁ = Γ₁} q₂ lf (unfoc p f) refl refl ξ)) =
  foc s q (focl q₂ (untag-lf lf) (focr {Γ₀ = untag-cxt Γ₁} _ rf (unfoc (inj₁ p) (untag⇑ {Γ = ∘tcxt Γ₁} f)) refl) refl)
MF-only-rf-at _ x q rf (foc s q₁ (focr s' (⊗r+ Δ₀ Ξ m rf₁ gs) f eq eq' ξ)) =
  ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (map proj₂ Ξ)) (at→negat x))
MF-only-rf-at _ x q rf (foc s q₁ (focr {Γ₁ = []} ._ blurr f refl refl ξ)) =
  foc s q (focr (just _) rf (untag⇓ f) refl)

MF-only-rf : {S : Stp} (Δ₀ : TCxt) {Δ₁ : Cxt} {M Q : Fma}
             (m : isNegAt M) (q : isPosAt Q)
             (rf : just (M , m) MMF.⇛rf Δ₁ ； Q) 
             (f : (∘ , S) MMF.∣ Δ₀ ⇑ (∘ , M)) → S MF.∣ untag-cxt Δ₀ ++ Δ₁ ⇑ Q
MF-only-rf Δ₀ {M = ` X} m q rf f = MF-only-rf-at Δ₀ tt q (untag-rf rf) f
MF-only-rf Δ₀ {M = A ⊸ B} m q rf f = MF-only-rfN (untag-cxt Δ₀) [] tt q (untag-rf rf) (untag⇑ f)

gen-early-rf : ∀ {S Γ₁ Γ₂ Δ} Δ' {N Q R n} {q : isPos Q} {r}
            {rf : just (Δ' ⊸⋆ N , neg→negat n) MF.⇛rf Γ₂ ； R}
            (f : S MF.∣ Δ ++ Γ₁ ++ Δ' ⇑ N) (ℓ : L S Δ Q) →
            unfoc {∙}{∘} q (MF.runL {Δ = Γ₁ ++ Γ₂} ℓ (MF-only-rfN (Δ ++ Γ₁) Δ' n r rf f))
              ≗⇓ focr {∙} _ rf (unfoc {∙}{∙} (inj₁ q) (MF.⊸r⋆⇑ Δ' (MF.runL ℓ f))) refl
gen-early-rf Δ' (⊸r f) ℓ =
  gen-early-rf (Δ' ∷ʳ _) f ℓ
  • focr refl-rf (unfoc-same (refl⇑ (trans (EqC.⊸r⋆⊸r⋆⇑ Δ' {_ ∷ []})
                                    (cong (MF.⊸r⋆⇑ Δ') (EqC.⊸r⋆runL (_ ∷ []) ℓ)))))
gen-early-rf Δ' (Il q f) ℓ =
  unfoc-same (congrunL ℓ (refl⇑ (sym (EqC.Il⇑eq _))))
  • gen-early-rf Δ' f (Il-1 ℓ)
  • focr refl-rf (unfoc-same (refl⇑ (cong (MF.⊸r⋆⇑ Δ') (cong (MF.runL ℓ) (EqC.Il⇑eq _)))))
gen-early-rf Δ' (⊗l q f) ℓ =
  unfoc-same (congrunL ℓ (refl⇑ (sym (EqC.⊗l⇑eq _))))
  • gen-early-rf Δ' f (⊗l-1 ℓ)
  • focr refl-rf (unfoc-same (refl⇑ (cong (MF.⊸r⋆⇑ Δ') (cong (MF.runL ℓ) (EqC.⊗l⇑eq _)))))
gen-early-rf Δ' (foc s q f) ℓ =
  early-rf s ℓ
  • focr refl-rf (unfoc-same (refl⇑ (sym (EqC.⊸r⋆runL Δ' ℓ))))

gen-early-rf-at : ∀ {S Γ₁ Γ₂ Δ X Q R x} {q : isPos Q} {r}
                {rf : just (X , at→negat x) MF.⇛rf Γ₂ ； R}
                (f : (∘ , S) MMF.∣ ∘cxt Δ ++ Γ₁ ⇑ (∘ , X)) (ℓ : L S Δ Q) →
              unfoc {∙}{∘} q (MF.runL {Δ = untag-cxt Γ₁ ++ Γ₂} ℓ (MF-only-rf-at (∘cxt Δ ++ Γ₁) x r rf f))
              ≗⇓ focr {∙} _ rf (unfoc {∙}{∙} (inj₁ q) (MF.runL {Δ = untag-cxt Γ₁} ℓ (untag⇑ {Γ = ∘cxt Δ ++ Γ₁} f))) refl
gen-early-rf-at (Il q f) ℓ =
  unfoc-same (congrunL ℓ (refl⇑ (sym (EqC.Il⇑eq _))))
  • gen-early-rf-at f (Il-1 ℓ)
  • focr refl-rf (unfoc-same (congrunL ℓ (refl⇑ (EqC.Il⇑eq _))))
gen-early-rf-at (⊗l q f) ℓ = 
  unfoc-same (congrunL ℓ (refl⇑ (sym (EqC.⊗l⇑eq _))))
  • gen-early-rf-at f (⊗l-1 ℓ)
  • focr refl-rf (unfoc-same (congrunL ℓ (refl⇑ (EqC.⊗l⇑eq _))))
gen-early-rf-at {x = x} (foc s q (focl q₁ lf (focr s₁ (⊗r+ Δ₀ Ξ m rf gs) f eq₁ eq'' ξ₁) eq eq' ξ)) ℓ =
  ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (map proj₂ Ξ)) (at→negat x))
gen-early-rf-at {Γ₁ = Γ₂} {Δ = Δ} (foc s q (focl {Γ₀ = Γ₀} {Γ₁} q₁ lf (focr {Γ₁ = []} _ blurr f refl refl ξ₁) eq refl ξ)) ℓ with ++? Γ₀ (∘cxt Δ) Γ₁ Γ₂ eq
... | inj₂ (A , Ω , r , refl) with split-map ∘fma Δ Γ₀ (A ∷ Ω) r
gen-early-rf-at {Γ₁ = Γ₂} {Δ = .(Γ₀' ++ A' ∷ Ω')} {x = x} (foc s q (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₀')} {.((∘ , A') ∷ map (λ A → ∘ , A) Ω' ++ Γ₂)} q₁ lf (focr {_} {_} {_} {_} {_} {_} {[]} (just (_ , m)) blurr f refl refl ξ₁) refl refl ξ)) ℓ | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Ω') , r , refl) | Γ₀' , A' ∷ Ω' , refl , refl , refl
  rewrite isProp-isNegAt m (at→negat x) =
  unfoc-same (congrunL ℓ (foc-same swap))
  • early-rf-at s ℓ
  • focr refl-rf (unfoc-same (congrunL ℓ (foc (~ swap))))
gen-early-rf-at {S} {Γ₁ = .(Ω ++ Γ₁)} {Δ = Δ} {x = x} (foc s q (focl {Γ₀ = .(map (λ A → ∘ , A) Δ ++ Ω)} {Γ₁} q₁ lf (focr {_} {_} {_} {_} {_} {_} {[]} (just (_ , m)) blurr f refl refl ξ₁) refl refl ξ)) ℓ | inj₁ (Ω , refl , refl) 
  rewrite isProp-isNegAt m (at→negat x) =
  unfoc-same (congrunL ℓ (foc-same swap))
  • early-rf-at {Γ₁ = untag-cxt (Ω ++ Γ₁)} s ℓ
  • focr refl-rf (unfoc-same (congrunL ℓ (foc (~ swap))))
gen-early-rf-at {Γ₁ = Γ₂} {Δ = Δ} (foc s q (focl {Γ₀ = Γ₀} {Γ₁} q₁ lf (unfoc ok f) eq refl ξ)) ℓ with ++? Γ₀ (∘cxt Δ) Γ₁ Γ₂ eq
... | inj₂ (A , Ω , r , refl) with split-map ∘fma Δ Γ₀ (A ∷ Ω) r
gen-early-rf-at {Γ₁ = Γ₂} {Δ = .(Γ₀' ++ A' ∷ Ω')} {X = ` X}(foc s q (focl {Γ₀ = .(map (λ A → ∘ , A) Γ₀')} {.((∘ , A') ∷ map (λ A → ∘ , A) Ω' ++ Γ₂)} q₁ lf (unfoc ok f) refl refl ξ)) ℓ | inj₂ (.(∘ , A') , .(map (λ A → ∘ , A) Ω') , r , refl) | Γ₀' , A' ∷ Ω' , refl , refl , refl =
  unfoc-same (congrunL ℓ (foc-same swap))
  • early-rf-at s ℓ
  • focr refl-rf (unfoc-same (congrunL ℓ (foc (~ swap • focl refl-lf blurr-at))))
gen-early-rf-at {Γ₁ = .(Ω ++ Γ₁)} {Δ = Δ} {X = ` X} (foc s q (focl {Γ₀ = .(map (λ A → ∘ , A) Δ ++ Ω)} {Γ₁} q₁ lf (unfoc ok f) refl refl ξ)) ℓ | inj₁ (Ω , refl , refl) =
  unfoc-same (congrunL ℓ (foc-same swap))
  • early-rf-at {Γ₁ = untag-cxt (Ω ++ Γ₁)} s ℓ
  • focr refl-rf (unfoc-same (congrunL ℓ (foc (~ swap • focl refl-lf blurr-at))))
gen-early-rf-at {x = x} (foc s q (focr s₁ (⊗r+ Δ₀ Ξ m rf gs) f eq eq' ξ)) ℓ =
  ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (map proj₂ Ξ)) (at→negat x))
gen-early-rf-at {x = x} (foc s q (focr {Γ₁ = []} (just (_ , m)) blurr f refl refl ξ)) ℓ
  rewrite isProp-isPosAt q (at→posat x) | isProp-isNegAt m (at→negat x) = early-rf-at s ℓ

untag-only-rf-at : {S : Stp} (Δ₀ : TCxt) {Δ₁ : Cxt} {X Q : Fma}
              (x : isAt X) (q : isPosAt Q)
              (rf : just (X , at→negat x) MMF.⇛rf Δ₁ ； Q) 
              (f : (∘ , S) MMF.∣ Δ₀ ⇑ (∘ , X)) →
              untag⇑ (only-rf⇑-at Δ₀ x q rf f) ≗⇑ MF-only-rf-at Δ₀ x q (untag-rf rf) f
untag-only-rf-at Δ₀ x q rf (Il q₁ f) = Il (untag-only-rf-at Δ₀ x q rf f)
untag-only-rf-at Δ₀ x q rf (⊗l q₁ f) = ⊗l (untag-only-rf-at (_ ∷ Δ₀) x q rf f)
untag-only-rf-at Δ₀ x q rf (foc s q₁ (focl q₂ lf (focr s₁ (⊗r+ Δ₁ Ξ m rf₁ gs) f eq₁ eq'' ξ₁) eq eq' ξ)) = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (map proj₂ Ξ)) (at→negat x))
untag-only-rf-at _ x q rf (foc s q₁ (focl q₂ lf (focr {Γ₁ = []} .(just (_ , _)) blurr f refl refl ξ₁) refl refl ξ)) = refl⇑'
untag-only-rf-at _ x q rf (foc s q₁ (focl q₂ lf (unfoc ok f) refl refl ξ)) =
  foc-same (focl refl-lf (focr refl-rf (unfoc-same (refl⇑ (untag-r∙→∘⇑ f)))))
untag-only-rf-at Δ₀ x q rf (foc s q₁ (focr s₁ (⊗r+ Δ₁ Ξ m rf₁ gs) f eq eq' ξ)) = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (map proj₂ Ξ)) (at→negat x))
untag-only-rf-at Δ₀ x q rf (foc s q₁ (focr {Γ₁ = []} .(just (_ , _)) blurr f refl refl ξ)) = refl⇑'

untag-only-rf⇑ : {S : Stp} (Δ₀ : TCxt) {Δ₁ : Cxt} {M Q : Fma}
              (m : isNegAt M) (q : isPosAt Q)
              (rf : just (M , m) MMF.⇛rf Δ₁ ； Q) 
               (f : (∘ , S) MMF.∣ Δ₀ ⇑ (∘ , M)) →
               untag⇑ (only-rf⇑ Δ₀ m q rf f) ≗⇑ MF-only-rf Δ₀ m q rf f

untag-only-rfN : {S : Stp} (Δ₀ : TCxt) {Δ₁ : Cxt} (Γ : Cxt) {B Q : Fma}
               (n : isNeg (Γ ⊸⋆ B)) (q : isPosAt Q)
               (rf : just (Γ ⊸⋆ B , neg→negat n) MMF.⇛rf Δ₁ ； Q) 
               (f : (∘ , S) MMF.∣ Δ₀ ++ ∘cxt Γ ⇑ (∘ , B)) →
               untag⇑ (only-rf⇑N Δ₀ Γ n q rf f) ≗⇑ MF-only-rfN (untag-cxt Δ₀) Γ n q (untag-rf rf) (untag⇑ {Γ = Δ₀ ++ ∘cxt Γ} f)

untag-only-rf-fN : {S : Stp} {Δ : TCxt} (Δ₀ : TCxt) {Δ₁ : Cxt} (Γ : Cxt) {Q Q' : Fma}
               (s : isIrr S) (n : isNeg (Γ ⊸⋆ Q')) (q : isPosAt Q) (q' : isPosAt Q')
               (rf : just (Γ ⊸⋆ Q' , neg→negat n) MMF.⇛rf Δ₁ ； Q) 
               (f : MMF.[ ∘ , ∘ ] (∘ , S) ∣ Δ ⇓ (∘ , Q'))
               (eq : Δ ≡ Δ₀ ++ ∘cxt Γ) →
               untag⇓ (only-rf-fN Δ₀ Γ s n q q' rf f eq) ≗⇓
                 focr _ (untag-rf rf) (unfoc n (MF.⊸r⋆⇑ Γ (foc s q' (untag⇓ {Γ = Δ₀ ++ ∘cxt Γ} (subst⇓ f eq))))) refl

untag-only-rf⇑ Δ₀ {M = ` X} m q rf f = untag-only-rf-at Δ₀ tt q rf f
untag-only-rf⇑ Δ₀ {M = A ⊸ B} m q rf f = untag-only-rfN Δ₀ [] tt q rf f

untag-only-rfN Δ₀ Γ n q rf (⊸r f) = untag-only-rfN Δ₀ (Γ ∷ʳ _) n q rf f
untag-only-rfN Δ₀ Γ n q rf (Il q₁ f) = Il (untag-only-rfN Δ₀ Γ n q rf f)
untag-only-rfN Δ₀ Γ n q rf (⊗l q₁ f) = ⊗l (untag-only-rfN (_ ∷ Δ₀) Γ n q rf f)
untag-only-rfN Δ₀ Γ n q rf (foc s q₁ f) = foc-same (untag-only-rf-fN Δ₀ Γ s n q q₁ rf f refl)

untag-only-rf-fN Δ₀ {Δ₁} Γ s n q q' rf (focl {Γ₀ = Γ₀} {Γ₁} q₁ lf (focr (just (._ , snd)) rf₁ ax refl refl ξ₁) refl refl ξ) eq with ++? _ Γ₀ (∘cxt Γ) Γ₁ eq
untag-only-rf-fN .(Γ₀ ++ Λ) {Δ₁} Γ s n q q' rf (focl {Γ₀ = Γ₀} {.(Λ ++ map (λ A → ∘ , A) Γ)} q₁ lf (focr (just (.(` _) , snd)) rf₁ ax refl refl ξ₁) refl refl ξ) refl | inj₁ (Λ , refl , refl) =
  swap
  • focr refl-rf
         (focl refl-lf {eq' = refl} (unfoc-same (refl⇑ (untag-⊸r⋆⇑ {Γ = ∘tcxt Λ} Γ _)))
         • ~ early-lf-at Γ q')
... | inj₂ (A , Λ , refl , eq') with split-map ∘fma Γ (_ ∷ Λ) Γ₁ eq'
untag-only-rf-fN Δ₀ {Δ₁} .((_ ∷ Λ') ++ Γ₁') s n q q' rf (focl {_} {_} {_} {_} {.(Δ₀ ++ (∘ , _) ∷ map (λ A → ∘ , A) Λ')} {.(map (λ A → ∘ , A) Γ₁')} q₁ lf (focr (just (.(` _) , snd)) rf₁ ax refl refl ξ₁) refl refl ξ) refl | inj₂ (.(∘ , _) , .(map (λ A → ∘ , A) Λ') , refl , eq') | _ ∷ Λ' , Γ₁' , refl , refl , refl =
  focr refl-rf (unfoc-same (⊸r (refl⇑ (untag-⊸r⋆⇑ {Γ = ∘tcxt Δ₀ ∷ʳ _} (Λ' ++ Γ₁') _))))
untag-only-rf-fN _ {Δ₁} Γ s n q q' rf (focl {Γ₀ = Γ₀} q₁ lf (focr {Γ₀ = Γ₁} {Γ₂} (just (M , m)) rf₁ (unfoc ok f) refl refl ξ₁) refl refl ξ) eq with ++? _ Γ₀ (∘cxt Γ) (Γ₁ ++ Γ₂) eq
... | inj₁ (Λ , eq' , refl) with ++? Λ Γ₁ (∘cxt Γ) Γ₂ eq'
untag-only-rf-fN .(Γ₀ ++ Γ₁ ++ Λ') {Δ₁} Γ s n q q' rf (focl {Γ₀ = Γ₀} {Q = Q} q₁ lf (focr {Γ₀ = Γ₁} {.(Λ' ++ map (λ A → ∘ , A) Γ)} (just (` X , m)) rf₁ (unfoc (inj₁ p) f) refl refl ξ₁) refl refl ξ) refl | inj₁ (.(Γ₁ ++ Λ') , eq' , refl) | inj₁ (Λ' , refl , refl)
  rewrite isProp-isPosAt q₁ (pos→posat p) = 
  swap
  • focr refl-rf {eq' = refl}
         (focl refl-lf {eq' = refl} (unfoc-same (refl⇑ (untag-⊸r⋆⇑ {Γ = ∘tcxt (Γ₁ ++ Λ')} Γ _))))
         • focr refl-rf (focl refl-lf {eq' = refl} (unfoc-same (cong⊸r⋆⇑ Γ (untag-only-rf-at (∘tcxt Γ₁) m q' rf₁ f)))
                        • (~ (early-lf Γ q' {eq' = refl} ))
                        • unfoc-same (cong⊸r⋆⇑ Γ (foc-same (focl refl-lf (gen-early-rf-at {Γ₁ = ∘tcxt _} f done)))))
untag-only-rf-fN .(Γ₀ ++ Γ₁ ++ Λ') {Δ₁} Γ s n q q' rf (focl {Γ₀ = Γ₀} q₁ lf (focr {Γ₀ = Γ₁} {.(Λ' ++ map (λ A → ∘ , A) Γ)} (just (_ ⊸ _ , m)) rf₁ (unfoc (inj₁ p) f) refl refl ξ₁) refl refl ξ) refl | inj₁ (.(Γ₁ ++ Λ') , eq' , refl) | inj₁ (Λ' , refl , refl) 
  rewrite isProp-isPosAt q₁ (pos→posat p) = 
  swap
  • focr refl-rf {eq' = refl}
        (focl refl-lf {eq' = refl} (unfoc-same (refl⇑ (untag-⊸r⋆⇑ {Γ = ∘tcxt (Γ₁ ++ Λ')} Γ _))))
        • focr refl-rf (focl refl-lf {eq' = refl} (unfoc-same (cong⊸r⋆⇑ Γ (untag-only-rfN (∘tcxt Γ₁) [] tt q' rf₁ f)))
                       • (~ (early-lf Γ q' {eq' = refl} ))
                       • unfoc-same (cong⊸r⋆⇑ Γ (foc-same (focl refl-lf (gen-early-rf [] (untag⇑ f) done)))))
untag-only-rf-fN .(Γ₀ ++ Γ₁ ++ Λ') {Δ₁} Γ s n q q' rf (focl {Γ₀ = Γ₀} {Q = ` X} q₁ lf (focr {Γ₀ = Γ₁} {.(Λ' ++ map (λ A → ∘ , A) Γ)} (just (_ ⊸ _ , m)) rf₁ (unfoc (inj₂ (x , n')) f) refl refl ξ₁) refl refl ξ) refl | inj₁ (.(Γ₁ ++ Λ') , eq' , refl) | inj₁ (Λ' , refl , refl) = 
  swap
  • focr refl-rf {eq' = refl}
         (focl refl-lf {eq' = refl} (unfoc-same (refl⇑ (untag-⊸r⋆⇑ {Γ = ∘tcxt (Γ₁ ++ Λ')} Γ _))))
         • focr refl-rf (focl refl-lf {eq' = refl} (unfoc-same (cong⊸r⋆⇑ Γ (trans⇑ (untag-only-rfN (∘tcxt Γ₁) [] tt q' rf₁ f)
                                                                                   (refl⇑ (MF-only-rfN-eq (untag-cxt Γ₁) [] tt m q' (untag-rf rf₁) (untag⇑ {Γ = ∘tcxt Γ₁} f))))))
                        • focl refl-lf {eq' = refl} (unfoc-same (cong⊸r⋆⇑ Γ (foc-same (focr refl-rf {eq' = refl} (~ blurl-at) • (~ swap)))))
                        • (~ (early-lf-at Γ q' {eq' = refl}))
                        • refl)
... | inj₂ (A' , Λ' , refl , eq'') with split-map ∘fma Γ (_ ∷ Λ') Γ₂ eq''
untag-only-rf-fN .(Γ₀ ++ Λ) {Δ₁} .((_ ∷ Λ'') ++ Γ₂') s n q q' rf (focl {Γ₀ = Γ₀} q₁ lf (focr {_} {_} {_} {_} {_} {.(Λ ++ (∘ , _) ∷ map (λ A → ∘ , A) Λ'')} {.(map (λ A → ∘ , A) Γ₂')} (just (` _ , m)) rf₁ (unfoc (inj₁ p) f) refl refl ξ₁) refl refl ξ) refl | inj₁ (Λ , eq' , refl) | inj₂ (.(∘ , _) , .(map (λ A → ∘ , A) Λ'') , refl , eq'') | _ ∷ Λ'' , Γ₂' , refl , refl , refl 
  rewrite isProp-isPosAt q₁ (pos→posat p) = 
  swap
  • focr refl-rf {eq' = refl}
         (focl refl-lf {eq' = refl} (unfoc-same (refl⇑ (untag-⊸r⋆⇑ {Γ = ∘tcxt Λ} (_ ∷ Λ'' ++ Γ₂') _))))
         • focr refl-rf (focl refl-lf {eq' = refl} (unfoc-same (cong⊸r⋆⇑ (_ ∷ Λ'' ++ Γ₂') (untag-only-rf-at (∘tcxt Λ ++ _ ∷ ∘cxt Λ'') m q' rf₁ f)))
                        • (~ (early-lf (_ ∷ Λ'' ++ Γ₂') q' {eq' = refl} ))
                        • unfoc-same (cong⊸r⋆⇑ (_ ∷ Λ'' ++ Γ₂') (foc-same (focl refl-lf (gen-early-rf-at {Γ₁ = ∘tcxt _ ++ _ ∷ ∘cxt Λ''} f done)))))
untag-only-rf-fN .(Γ₀ ++ Λ) {Δ₁} .((_ ∷ Λ'') ++ Γ₂') s n q q' rf (focl {Γ₀ = Γ₀} q₁ lf (focr {_} {_} {_} {_} {_} {.(Λ ++ (∘ , _) ∷ map (λ A → ∘ , A) Λ'')} {.(map (λ A → ∘ , A) Γ₂')} (just (_ ⊸ _ , m)) rf₁ (unfoc (inj₁ p) f) refl refl ξ₁) refl refl ξ) refl | inj₁ (Λ , eq' , refl) | inj₂ (.(∘ , _) , .(map (λ A → ∘ , A) Λ'') , refl , eq'') | _ ∷ Λ'' , Γ₂' , refl , refl , refl 
  rewrite isProp-isPosAt q₁ (pos→posat p) = 
  swap
  • focr refl-rf {eq' = refl}
        (focl refl-lf {eq' = refl} (unfoc-same (refl⇑ (untag-⊸r⋆⇑ {Γ = ∘tcxt Λ} (_ ∷ Λ'' ++ Γ₂') _))))
        • focr refl-rf (focl refl-lf {eq' = refl} (unfoc-same (cong⊸r⋆⇑ (_ ∷ Λ'' ++ Γ₂') (untag-only-rfN (∘tcxt Λ ++ _ ∷ ∘cxt Λ'') [] tt q' rf₁ f)))
                       • (~ (early-lf (_ ∷ Λ'' ++ Γ₂') q' {eq' = refl} ))
                       • unfoc-same (cong⊸r⋆⇑ (_ ∷ Λ'' ++ Γ₂') (foc-same (focl refl-lf (gen-early-rf [] (untag⇑ f) done)))))
untag-only-rf-fN .(Γ₀ ++ Λ) {Δ₁} .((_ ∷ Λ'') ++ Γ₂') s n q q' rf (focl {Γ₀ = Γ₀} {Q = ` X} q₁ lf (focr {_} {_} {_} {_} {_} {.(Λ ++ (∘ , _) ∷ map (λ A → ∘ , A) Λ'')} {.(map (λ A → ∘ , A) Γ₂')} (just (_ ⊸ _ , m)) rf₁ (unfoc (inj₂ (x , n')) f) refl refl ξ₁) refl refl ξ) refl | inj₁ (Λ , eq' , refl) | inj₂ (.(∘ , _) , .(map (λ A → ∘ , A) Λ'') , refl , eq'') | _ ∷ Λ'' , Γ₂' , refl , refl , refl =
  swap
  • focr refl-rf {eq' = refl}
         (focl refl-lf {eq' = refl} (unfoc-same (refl⇑ (untag-⊸r⋆⇑ {Γ = ∘tcxt Λ} (_ ∷ Λ'' ++ Γ₂') _))))
         • focr refl-rf (focl refl-lf {eq' = refl} (unfoc-same (cong⊸r⋆⇑ (_ ∷ Λ'' ++ Γ₂') (trans⇑ (untag-only-rfN (∘tcxt Λ ++ _ ∷ ∘cxt Λ'') [] tt q' rf₁ f)
                                                                                   (refl⇑ (MF-only-rfN-eq (untag-cxt ((∘tcxt Λ ++ ∘fma _ ∷ ∘cxt Λ''))) [] tt m q' (untag-rf rf₁) (untag⇑ {Γ = ∘tcxt Λ ++ _ ∷ ∘cxt Λ''} f))))))
                        • focl refl-lf {eq' = refl} (unfoc-same (cong⊸r⋆⇑ (_ ∷ Λ'' ++ Γ₂') (foc-same (focr refl-rf {eq' = refl} (~ blurl-at) • (~ swap)))))
                        • (~ (early-lf-at (_ ∷ Λ'' ++ Γ₂') q' {eq' = refl}))
                        • refl)
untag-only-rf-fN Δ₀ {Δ₁} Γ s n q q' rf (focl q₁ lf (focr {Γ₀ = Γ₁} {Γ₂} (just x) rf₁ (unfoc ok f) refl refl ξ₁) refl refl ξ) eq | inj₂ (A , Λ , refl , eq') with split-map ∘fma Γ (_ ∷ Λ) (Γ₁ ++ Γ₂) eq'
... | _ ∷ Λ' , Ω , refl , eq'' , refl with split-map ∘fma Ω Γ₁ Γ₂ eq''
untag-only-rf-fN Δ₀ {Δ₁} .((_ ∷ Λ') ++ Γ₁' ++ Γ₂') s n q q' rf (focl {_} {_} {_} {_} {.(Δ₀ ++ (∘ , _) ∷ map _ Λ')} q₁ lf (focr {Γ₀ = .(map (λ A → ∘ , A) Γ₁')} {.(map (λ A → ∘ , A) Γ₂')} (just (_ , _)) rf₁ (unfoc ok f) refl refl ξ₁) refl refl ξ) refl | inj₂ (.(∘ , _) , .(map _ Λ') , refl , eq') | _ ∷ Λ' , .(Γ₁' ++ Γ₂') , refl , eq'' , refl | Γ₁' , Γ₂' , refl , refl , refl =
  focr refl-rf (unfoc-same (⊸r (refl⇑ (untag-⊸r⋆⇑ {Γ = ∘tcxt Δ₀ ∷ʳ _} (Λ' ++ Γ₁' ++ Γ₂') _))))
untag-only-rf-fN Δ₀ {Δ₁} Γ s n q q' rf (focl {Γ₀ = Γ₀} {Γ₁} q₁ lf (unfoc ok f) refl refl ξ) eq with ++? _ Γ₀ (∘cxt Γ) Γ₁ eq
untag-only-rf-fN .(Γ₀ ++ Λ) {Δ₁} Γ s n q q' rf (focl {Γ₀ = Γ₀} {.(Λ ++ map (λ A → ∘ , A) Γ)} q₁ lf (unfoc ok f) refl refl ξ) refl | inj₁ (Λ , refl , refl)
  rewrite isProp-isPosAt q₁ (pos→posat ok) =
  swap
  • focr refl-rf
         (focl refl-lf {eq' = refl} (unfoc-same (refl⇑ (trans (untag-⊸r⋆⇑ {Γ = ∘tcxt _} Γ _) (cong (MF.⊸r⋆⇑ Γ) (untag-r∙→∘⇑ f)))))
         • (~ early-lf Γ q'))
... | inj₂ (A , Λ , refl , eq') with split-map ∘fma Γ (_ ∷ Λ) Γ₁ eq'
untag-only-rf-fN Δ₀ {Δ₁} .((_ ∷ Λ') ++ Γ₁') s n q q' rf (focl {_} {_} {_} {_} {.(Δ₀ ++ (∘ , _) ∷ map (λ A → ∘ , A) Λ')} {.(map (λ A → ∘ , A) Γ₁')} q₁ lf (unfoc ok f) refl refl ξ) refl | inj₂ (.(∘ , _) , .(map (λ A → ∘ , A) Λ') , refl , eq') | _ ∷ Λ' , Γ₁' , refl , refl , refl =
  focr refl-rf (unfoc-same (⊸r (refl⇑ (untag-⊸r⋆⇑ {Γ = ∘tcxt Δ₀ ∷ʳ _} (Λ' ++ Γ₁') _))))
untag-only-rf-fN _ {Δ₁} Γ s n q q' rf (focr {Γ₀ = Γ₀} {Γ₁} (just (M , m)) rf₁ (unfoc ok f) refl refl ξ) eq with ++? _ Γ₀ (∘cxt Γ) Γ₁ eq
untag-only-rf-fN _ {Δ₁} Γ s n q q' rf (focr {Γ₀ = Γ₀} {.(Λ ++ map (λ A → ∘ , A) Γ)} (just (M , m)) rf₁ (unfoc ok f) refl refl ξ) refl | inj₁ (Λ , refl , refl) =
  focr refl-rf (unfoc-same (refl⇑ (untag-⊸r⋆⇑ {Γ = ∘tcxt (Γ₀ ++ Λ)} Γ _)))
... | inj₂ (A , Λ , refl , eq') with split-map ∘fma Γ (_ ∷ Λ) Γ₁ eq'
untag-only-rf-fN _ {Δ₁} .((_ ∷ Λ') ++ Γ₁') s n q q' rf (focr {_} {_} {_} {_} {_} {.(_ ++ (∘ , _) ∷ map (λ A → ∘ , A) Λ')} {.(map (λ A → ∘ , A) Γ₁')} (just (M , m)) rf₁ (unfoc ok f) refl refl ξ) refl | inj₂ (.(∘ , _) , .(map (λ A → ∘ , A) Λ') , refl , eq') | _ ∷ Λ' , Γ₁' , refl , refl , refl =
  focr refl-rf (unfoc-same (⊸r (refl⇑ (untag-⊸r⋆⇑ {Γ = ∘tcxt _ ∷ʳ _} (Λ' ++ Γ₁') _))))
untag-only-rf-fN _ {Δ₁} Γ s n q q' rf (focr ─ rf₁ (refl , refl) refl refl ξ) refl =
  focr refl-rf (unfoc-same (refl⇑ (untag-⊸r⋆⇑ {Γ = ∘tcxt _} Γ _)))

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

untag-only-lf-at : {S : Stp} {Δ₀ : Cxt} (Δ₁ : TCxt) {X C : Fma}
               (s : isIrr S) (x : isAt X)
               (lf : at→posat x ⇛lf S ∣ Δ₀) 
               (f : (∘ , just X) MMF.∣ Δ₁ ⇑ (∘ , C)) →
               untag⇑ (only-lf⇑-at Δ₁ s x lf f) ≗⇑ MF-only-lf-at Δ₁ s x (untag-lf lf) f
untag-only-lf-at Δ₁ s x lf (⊸r f) = ⊸r (untag-only-lf-at (Δ₁ ∷ʳ _) s x lf f)
untag-only-lf-at Δ₁ s x lf (foc s₁ q (focl {Γ₀ = []} q₁ blurl f refl refl ξ)) = refl⇑'
untag-only-lf-at _ s x lf (foc s₁ q (focr (just (M , m)) rf (unfoc ok f) refl refl ξ)) =
  foc-same (focl refl-lf (focr refl-rf (unfoc-same (refl⇑ (untag-l∙→∘⇑ f)))))

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
                 (trans⇑ (refl⇑ (MF-only-lfP-eq Γ₁ s ok q _ _ done))
                         (foc-same (focl (untag∘max-lf lf) (unfoc-same (untag⇑∘max f)))))) 
untag⇑∘max (foc s q (focr (just (.(` _) , snd)) rf (focl q₁ lf ax refl) refl)) = foc (swap • focr (untag∘max-rf rf) (focl (untag∘max-lf lf) refl))
untag⇑∘max (foc s q (focr (just x) rf (focl q₁ lf (unfoc ok f) refl) refl)) = foc (swap • focr (untag∘max-rf rf) (focl (untag∘max-lf lf) (unfoc (untag⇑∘max f))))
untag⇑∘max (foc s q (focr {Γ₀ = Γ₀} {Γ₁} (just (M , m)) rf (unfoc n f) refl))
  rewrite isProp-isNegAt m (neg→negat n) =
  trans⇑ (refl⇑ (cong (untag⇑ {Γ = ∘cxt (Γ₀ ++ Γ₁)}) (only-rf⇑eq n (max f))))
         (trans⇑ (untag-only-rfN (∘cxt Γ₀) [] n q (max-rf rf) (max f))
                 (trans⇑ (refl⇑ (MF-only-rfN-eq Γ₀ [] s n q _ _))
                         (foc-same (focr (untag∘max-rf rf) (unfoc-same (untag⇑∘max f))))))
untag⇑∘max (foc s q (focr ─ rf (refl , refl) refl)) = foc (focrn (untag∘max-rf rf))








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

-- cong-MF-only-lfP₁ : {S S' : Stp} {Γ Δ₀ : Cxt} (Δ₁ : Cxt) {P C : Fma}
--                    (s : isIrr S) (p : isPos P) 
--                    {h k : pos→posat p ⇛lf S ； Δ₀} (eq : h ≗lf k)
--                    (f : S' MF.∣ Γ ++ Δ₁ ⇑ C)
--                    (ℓ : MF.L S' Γ P) →
--                    MF-only-lfP Δ₁ s p h f ℓ ≗⇑ MF-only-lfP Δ₁ s p k f ℓ
-- cong-MF-only-lfP₁ Δ₁ s p eq (⊸r f) ℓ = ⊸r (cong-MF-only-lfP₁ (Δ₁ ∷ʳ _) s p eq f ℓ)
-- cong-MF-only-lfP₁ Δ₁ s p eq (Il q f) ℓ = foc-same (focl eq refl)
-- cong-MF-only-lfP₁ Δ₁ s p eq (⊗l q f) ℓ = foc-same (focl eq refl)
-- cong-MF-only-lfP₁ Δ₁ s p eq (foc s₁ q f) ℓ = foc-same (focl eq refl)
-- 
-- cong-MF-only-lfP₂ : {S S' : Stp} {Γ Δ₀ : Cxt} (Δ₁ : Cxt) {P C : Fma}
--                    (s : isIrr S) (p : isPos P) 
--                    (lf : pos→posat p ⇛lf S ； Δ₀)
--                    {f g : S' MF.∣ Γ ++ Δ₁ ⇑ C} (eq : f ≗⇑ g)
--                    (ℓ : MF.L S' Γ P) →
--                    MF-only-lfP Δ₁ s p lf f ℓ ≗⇑ MF-only-lfP Δ₁ s p lf g ℓ
-- cong-MF-only-lfP₂ Δ₁ s p lf (⊸r eq) ℓ = ⊸r (cong-MF-only-lfP₂ (Δ₁ ∷ʳ _) s p lf eq ℓ)
-- cong-MF-only-lfP₂ Δ₁ s p lf (Il eq) ℓ = foc (focl refl-lf (unfoc-same (congrunL ℓ (Il eq))))
-- cong-MF-only-lfP₂ Δ₁ s p lf (⊗l eq) ℓ = foc (focl refl-lf (unfoc-same (congrunL ℓ (⊗l eq))))
-- cong-MF-only-lfP₂ Δ₁ s p lf (foc eq) ℓ = foc (focl refl-lf (unfoc-same (congrunL ℓ (foc eq))))
-- 
-- cong-MF-only-lfP : {S S' : Stp} {Γ Δ₀ : Cxt} (Δ₁ : Cxt) {P C : Fma}
--                    (s : isIrr S) (p : isPos P) 
--                    {h k  : pos→posat p ⇛lf S ； Δ₀} (eq : h ≗lf k)
--                    {f g : S' MF.∣ Γ ++ Δ₁ ⇑ C} (eq' : f ≗⇑ g)
--                    (ℓ : MF.L S' Γ P) →
--                    MF-only-lfP Δ₁ s p h f ℓ ≗⇑ MF-only-lfP Δ₁ s p k g ℓ
-- cong-MF-only-lfP Δ₁ s p {k = k} eq {f} eq' ℓ =
--   trans⇑ (cong-MF-only-lfP₁ Δ₁ s p eq f ℓ) (cong-MF-only-lfP₂ Δ₁ s p k eq' ℓ)
