{-# OPTIONS --rewriting #-}

module correct.max-multifocus.EqComplete where

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

congfoc : {l r : Tag} {S : Stp} {Γ : TCxt} {Q : Fma}
        {s : isIrr S} {q : isPosAt Q}
        {f g : MMF.[ ∘ , ∘ ] (l , S) ∣ Γ ⇓ (r , Q)} → f ≡ g
        → MMF.foc s q f ≡ MMF.foc s q g
congfoc refl = refl        

congfocl : {l : Tag} {S : Stp} {Γ' : Cxt} {Γ Γ₀ Γ₁ : TCxt} {C : TFma} {Q : Fma}
         {q : isPosAt Q}
         {h k : q MMF.⇛lf S ∣ Γ'} → h ≡ k → 
         {f g : MMF.[ ∙ , ∘ ] (∘ , just Q) ∣ Γ₁ ⇓ C} → f ≡ g →
         {eq : Γ ≡ Γ₀ ++ Γ₁}
         {eq' : Γ' ≡ untag-cxt Γ₀}
         {ξ : ltag Γ₀ l} →
         MMF.focl {l = l} q h f eq eq' ξ ≡ MMF.focl q k g eq eq' ξ
congfocl refl refl = refl

congfocr : {b r : Tag} {S : TStp} {Γ' : Cxt} {Γ Γ₀ Γ₁ : TCxt} {C : Fma}
         {s : Maybe (Σ Fma isNegAt)}
         {h k : s MMF.⇛rf Γ' ； C} → h ≡ k → 
         {f g : MMF.end-rf? (λ T Δ A → MMF.[ b , ∙ ] T ∣ Δ ⇓ (∘ , A)) S Γ₀ s} → f ≡ g → 
         {eq : Γ ≡ Γ₀ ++ Γ₁}
         {eq' : Γ' ≡ untag-cxt Γ₁}
         {ξ : rtag s Γ₁ r} →
         MMF.focr s h f eq eq' ξ ≡ MMF.focr s k g eq eq' ξ
congfocr refl refl = refl         

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

only-rf⇑N-at≡ : (Δ₀ : TCxt) {Δ₁ : Cxt} (Γ : Cxt) {B Q X : Fma} {x : isAt X}
  (n : isNeg (Γ ⊸⋆ B)) (q : isPosAt Q)
  (rf : just (Γ ⊸⋆ B , neg→negat n) MMF.⇛rf Δ₁ ； Q) 
  (f : (∘ , just X) MMF.∣ Δ₀ ++ ∘cxt Γ ⇑ (∘ , B)) → 
 ------------------------------------
  only-rf⇑N Δ₀ Γ n q rf f
    ≡ foc (at→negat x) q (focl (at→posat x) blurl (focr {Γ₁ = ∘cxt Δ₁} (just (_ , (neg→negat n))) rf (unfoc (inj₂ n) (MMF.⊸r⋆⇑ Γ (untag-seq {Γ = Δ₀ ++ ∘cxt Γ} f))) refl refl tt) refl refl tt)

only-rf-fN-at≡ : {Δ : TCxt} (Δ₀ : TCxt) {Δ₁ : Cxt} (Γ : Cxt) {Q Q' X : Fma} {x : isAt X}
  (n : isNeg (Γ ⊸⋆ Q')) (q : isPosAt Q) (q' : isPosAt Q')
  (rf : just (Γ ⊸⋆ Q' , neg→negat n) MMF.⇛rf Δ₁ ； Q) 
  (f : MMF.[ ∘ , ∘ ] (∘ , just X) ∣ Δ ⇓ (∘ , Q'))
  (eq : Δ ≡ Δ₀ ++ ∘cxt Γ) → 
 ------------------------------------
  only-rf-fN Δ₀ Γ (at→negat x) n q q' rf f eq
    ≡ focl (at→posat x) blurl (focr {Γ₁ = ∘cxt Δ₁} (just (_ , (neg→negat n))) rf (unfoc (inj₂ n) (MMF.⊸r⋆⇑ Γ (foc (at→negat x) q' (untag-seq-f {Γ = Δ₀ ++ ∘cxt Γ} (subst⇓ f eq))))) refl refl tt) refl refl tt
 
only-rf⇑N-at≡ Δ₀ Γ n q rf (⊸r f) =
  trans (only-rf⇑N-at≡ Δ₀ (Γ ∷ʳ _) n q rf f)
        (congfoc (congfocl refl (congfocr refl (cong (unfoc (inj₂ n)) (⊸r⋆⊸r⋆⇑ Γ (_ ∷ []) (untag-seq f))))))
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
  congfocl refl (congfocr refl (cong (unfoc (inj₂ tt)) (cong (MMF.⊸r⋆⇑ (_ ∷ Ω' ++ Γ₁'))
    (trans (only-rf⇑N-at≡ (∘tcxt Δ₀ ++ ∘cxt (A ∷ Ω')) [] tt q' rf₁ f)
           (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘tcxt Δ₀ ++ ∘cxt (A ∷ Ω')} (inj₂ tt)) (untag-seq≡ {Γ = Δ₀ ++ ∘cxt (A ∷ Ω')}{∘tcxt Δ₀ ++ ∘cxt (A ∷ Ω')} f refl)))))))))
only-rf-fN-at≡ Δ₀ Γ {x = x} n q q' rf (focl q₁ blurl (unfoc ok f) eq₁ eq' ξ) eq = ⊥-elim (pos×negat→⊥ ok (at→negat x))
only-rf-fN-at≡ Δ₀ Γ n q q' rf (focl {Γ₀ = x₁ ∷ Γ₀} q₁ blurl (focr (just x) rf₁ (unfoc ok f) refl refl ξ₁) refl () ξ) eq
only-rf-fN-at≡ Δ₀ Γ {x = x} n q q' rf (focr (just (M , m)) rf₁ (unfoc ok f) eq₁ eq' ξ) eq = ⊥-elim (∙l⇑-at x f)

max⊸r⋆⇑ : {S : Stp} {Γ : Cxt} (Δ : Cxt) {A : Fma}
      (f : S MF.∣ Γ ++ Δ ⇑ A) →
      max (MF.⊸r⋆⇑ Δ f) ≡ MMF.⊸r⋆⇑ Δ (max {Γ = Γ ++ Δ} f)
max⊸r⋆⇑ [] f = refl
max⊸r⋆⇑ {Γ = Γ} (A ∷ Δ) f = cong ⊸r (max⊸r⋆⇑ {Γ = Γ ∷ʳ A} Δ f)

cong-only-rf⇑ : ∀ {S Δ₀ Δ₁ M Q m q}
              {rf : just (M , m) MMF.⇛rf Δ₁ ； Q}
              {f g : (∘ , S) MMF.∣ Δ₀ ⇑ (∘ , M)} → f ≡ g → 
              only-rf⇑ Δ₀ m q rf f ≡  only-rf⇑ Δ₀ m q rf g             
cong-only-rf⇑ refl = refl


only-rf⇑++ : ∀ {S Δ₀ Δ₁} Γ Γ' {A Q}
                {m : isNeg ((Γ ++ Γ') ⊸⋆ A)} {q : isPosAt Q}
                {rf : just ((Γ ++ Γ') ⊸⋆ A , neg→negat m) MMF.⇛rf Δ₁ ； Q}
                (f : (∘ , S) MMF.∣ Δ₀ ++ ∘cxt (Γ ++ Γ') ⇑ (∘ , A)) →
                only-rf⇑N Δ₀ (Γ ++ Γ') m q rf f ≡ only-rf⇑N Δ₀ Γ m q rf (MMF.⊸r⋆⇑ Γ' f)
only-rf⇑++ Γ [] f = refl
only-rf⇑++ Γ (A' ∷ Γ') f = only-rf⇑++ (Γ ∷ʳ A') Γ' f



only-rf⇑N-lf⇑P : ∀ {S S'} Γ Γ₀ Γ₁ Γ₂ Δ {P Q R}
  {s : isIrr S} {p : isPos P} {n : isNeg (Δ ⊸⋆ R)} {q : isPosAt Q}
  {lf : pos→posat p ⇛lf S ∣ Γ₀}
  {rf : just (Δ ⊸⋆ R , neg→negat n) MMF.⇛rf Γ₂ ； Q}
  (f : (∘ , S') MMF.∣ ∘cxt Γ ++ ∘cxt Γ₁ ++ ∘cxt Δ ⇑ (∘ , R)) → 
  (ℓ : MF.L S' Γ P) →
  only-rf⇑N (∘cxt (Γ₀ ++ Γ₁)) Δ n q rf (only-lf⇑P (∘cxt (Γ₁ ++ Δ)) s p lf f ℓ)  
    ≡ foc s q (focl {Γ₀ = ∘cxt Γ₀} (pos→posat p) lf (focr {Γ₀ = ∘cxt Γ₁} {Γ₁ = ∘cxt Γ₂} (just (Δ ⊸⋆ R , neg→negat n)) rf (unfoc (inj₁ p) (MMF.⊸r⋆⇑ Δ (MMF.runL ℓ f))) refl refl tt) refl refl tt)
only-rf⇑N-lf⇑P Γ Γ₀ Γ₁ Γ₂ Δ (⊸r f) ℓ =
  trans (only-rf⇑N-lf⇑P Γ Γ₀ Γ₁ Γ₂ (Δ ∷ʳ _) f ℓ) {!!}
only-rf⇑N-lf⇑P Γ Γ₀ Γ₁ Γ₂ Δ (Il q f) ℓ =
  trans (only-rf⇑N-lf⇑P Γ Γ₀ Γ₁ Γ₂ Δ f (Il-1 ℓ)) {!!}
only-rf⇑N-lf⇑P Γ Γ₀ Γ₁ Γ₂ Δ (⊗l q f) ℓ =
  trans (only-rf⇑N-lf⇑P (_ ∷ Γ) Γ₀ Γ₁ Γ₂ Δ f (⊗l-1 ℓ)) {!!}
only-rf⇑N-lf⇑P Γ Γ₀ Γ₁ Γ₂ Δ (foc s q f) ℓ = congfoc {!!}

{-
 only-rf⇑ (∘cxt (Γ₀ ++ Γ₁)) m q (max-rf h)
      (MMF.⊸r⋆⇑ Δ
       (only-lf⇑ (∘cxt (Γ₁ ++ Δ)) s (pos→posat q₁) (max-lf lf) (max f)))
      ≡
      foc s₁ q
      (focl (pos→posat q₁) (max-lf lf)
       (focr (just (Δ ⊸⋆ R , m)) (max-rf h)
        (unfoc (inj₁ q₁) (max (MF.⊸r⋆⇑ Δ f))) refl refl tt)
       refl refl tt)
-}

max≗⇑ : ∀ {S Γ A} {f g : S MF.∣ Γ ⇑ A} → f MF.≗⇑ g → max f ≡ max g
max≗⇓ : ∀ {S Γ Q s q} {f g : MF.[ ∘ , ∘ ] S ∣ Γ ⇓ Q}
  → f MF.≗⇓ g → max (foc s q f) ≡ max (foc s q g)
max≗⇓l₁ : ∀ {S Γ Γ₀ Γ₁ Q R s q r}
  → {h : r ⇛lf S ； Γ₀} 
  → {f g : MF.[ ∙ , ∘ ] just R ∣ Γ₁ ⇓ Q} → f MF.≗⇓ g
  → (eq : Γ ≡ Γ₀ ++ Γ₁)
  → max (foc s q (focl r h f eq)) ≡ max (foc s q (focl r h g eq)) 
max≗⇓l₂ : ∀ {S Γ Γ₀ Γ₁ Q R s q r}
  → {h k : r ⇛lf S ； Γ₀} → h ≗lf k
  → (f : MF.[ ∙ , ∘ ] just R ∣ Γ₁ ⇓ Q)
  → (eq : Γ ≡ Γ₀ ++ Γ₁)
  → max (foc s q (focl r h f eq)) ≡ max (foc s q (focl r k f eq)) 
max≗⇓lr₁ : ∀ {S Γ Γ' Γ₀ Γ₁ Γ₂ M Q R s q r m}
  → {h : r ⇛lf S ； Γ₀} {k : just (M , m) MF.⇛rf Γ₂ ； Q}
  → {f g : MF.[ ∙ , ∙ ] just R ∣ Γ₁ ⇓ M} → f MF.≗⇓ g
  → (eq : Γ ≡ Γ₀ ++ Γ') (eq' : Γ' ≡ Γ₁ ++ Γ₂)
  → max (foc s q (focl r h (focr (just (M , m)) k f eq') eq))
        ≡ max (foc s q (focl r h (focr (just (M , m)) k g eq') eq)) 
max≗⇓lr₂ : ∀ {S Γ Γ' Γ₀ Γ₁ Γ₂ M Q R s q r m}
  → {h : r ⇛lf S ； Γ₀} {k k' : just (M , m) MF.⇛rf Γ₂ ； Q} → k ≗rf k'
  → (f : MF.[ ∙ , ∙ ] just R ∣ Γ₁ ⇓ M)
  → (eq : Γ ≡ Γ₀ ++ Γ') (eq' : Γ' ≡ Γ₁ ++ Γ₂)
  → max (foc s q (focl r h (focr (just (M , m)) k f eq') eq))
        ≡ max (foc s q (focl r h (focr (just (M , m)) k' f eq') eq)) 
max≗⇓r₁ : ∀ {S Γ Γ₀ Γ₁ Q M s q m}
  → {f g : MF.[ ∘ , ∙ ] S ∣ Γ₀ ⇓ M} → f MF.≗⇓ g
  → {h : just (M , m) MF.⇛rf Γ₁ ； Q}
  → (eq : Γ ≡ Γ₀ ++ Γ₁)
  → max (foc s q (focr (just (M , m)) h f eq)) ≡ max (foc s q (focr (just (M , m)) h g eq))
max≗⇓r₂ : ∀ {S Γ Γ₀ Γ₁ Q M s q m}
  → (f : MF.[ ∘ , ∙ ] S ∣ Γ₀ ⇓ M)
  → {h k : just (M , m) MF.⇛rf Γ₁ ； Q} → h ≗rf k
  → (eq : Γ ≡ Γ₀ ++ Γ₁)
  → max (foc s q (focr (just (M , m)) h f eq)) ≡ max (foc s q (focr (just (M , m)) k f eq))
max≗⇓rl₁ : ∀ {S Γ Γ' Γ₀ Γ₁ Γ₂ M Q R s q r m}
  → {h : r ⇛lf S ； Γ₀} {k : just (M , m) MF.⇛rf Γ₂ ； Q}
  → {f g : MF.[ ∙ , ∙ ] just R ∣ Γ₁ ⇓ M} → f MF.≗⇓ g
  → (eq : Γ ≡ Γ' ++ Γ₂) (eq' : Γ' ≡ Γ₀ ++ Γ₁)
  → max (foc s q (focr (just (M , m)) k (focl r h f eq') eq))
        ≡ max (foc s q (focr (just (M , m)) k (focl r h g eq') eq))
max≗⇓rl₂ : ∀ {S Γ Γ' Γ₀ Γ₁ Γ₂ M Q R s q r m}
  → {h h' : r ⇛lf S ； Γ₀} → h ≗lf h' → {k : just (M , m) MF.⇛rf Γ₂ ； Q}
  → (f : MF.[ ∙ , ∙ ] just R ∣ Γ₁ ⇓ M)
  → (eq : Γ ≡ Γ' ++ Γ₂) (eq' : Γ' ≡ Γ₀ ++ Γ₁)
  → max (foc s q (focr (just (M , m)) k (focl r h f eq') eq))
        ≡ max (foc s q (focr (just (M , m)) k (focl r h' f eq') eq))
max≗lf : ∀ {S Γ Q} {q : isPosAt Q} {h k : q MF.⇛lf S ； Γ}
  → h ≗lf k → max-lf h ≡ max-lf k
max≗rf : ∀ {Γ A} {s : Maybe (Σ Fma isNegAt)} {h k : s MF.⇛rf Γ ； A}
  → h ≗rf k → max-rf h ≡ max-rf k
max≗⇑s : ∀ {Ξ} {fs gs : All (λ ΔB → ─ MF.∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ}
  → fs ≗s⇑ gs → maxs fs ≡ maxs gs

max≗⇓r₁ refl refl = refl
max≗⇓r₁ (~ eq) refl = sym (max≗⇓r₁ eq refl)
max≗⇓r₁ (eq • eq₁) refl = trans (max≗⇓r₁ eq refl) (max≗⇓r₁ eq₁ refl)
max≗⇓r₁ (focl eql {g = g} {eq = refl} {refl} eq) refl =
  trans (max≗⇓rl₁ eq refl refl) (max≗⇓rl₂ eql g refl refl)
max≗⇓r₁ (unfoc eq) refl = cong (only-rf⇑ _ _ _ _) (max≗⇑ eq)
max≗⇓r₁ (early-lf {Γ₀ = Γ₀} {Γ₁} [] {R = R} {n = n} r {eq = refl} {refl}) refl = ⊥-elim (neg×posat→⊥ n r)
max≗⇓r₁ (early-lf {Γ₀ = Γ₀} {Γ₁} (A' ∷ Δ) {I} r {eq = refl} {refl}) refl = 
  trans (cong (only-rf⇑ _ _ _ _) (max⊸r⋆⇑ {Γ = Γ₀ ++ Γ₁} (_ ∷ Δ) _))
        {!!}
max≗⇓r₁ (early-lf {Γ₀ = Γ₀} {Γ₁} (A' ∷ Δ) {P ⊗ P₁} r {eq = refl} {refl}) refl = 
  trans (cong (only-rf⇑ _ _ _ _) (max⊸r⋆⇑ {Γ = Γ₀ ++ Γ₁} (_ ∷ Δ) _))
        {!!}
max≗⇓r₁ (early-lf-at Δ r) refl = {!!}
max≗⇓r₁ {Γ₀ = Γ₀} {M = M ⊸ M₁} {q = q} (blurl-at {f = f}) {h} refl =
  sym (trans (only-rf⇑N-at≡ (∘cxt Γ₀) [] tt q (max-rf h) (max f))
             (congfoc (congfocl refl (congfocr refl (cong (unfoc {Γ = ∘cxt Γ₀} (inj₂ tt)) (untag-seq≡ {Γ = ∘cxt Γ₀} (max f) refl))))))

-- max≗⇓l₁ refl refl = refl
-- max≗⇓l₁ (~ eq) refl = sym (max≗⇓l₁ eq refl)
-- max≗⇓l₁ (eq • eq₁) refl = trans (max≗⇓l₁ eq refl) (max≗⇓l₁ eq₁ refl)
-- max≗⇓l₁ (focr eqr {g = g} {eq = refl} {eq' = refl} eq) refl =
--   trans (max≗⇓lr₁ eq refl refl) (max≗⇓lr₂ eqr g refl refl)
-- max≗⇓l₁ (unfoc eq) refl = cong (only-lf⇑ _ _ _ _) (max≗⇑ eq)
-- max≗⇓l₁ (early-rf t ℓ {refl}) refl = {!!}
-- max≗⇓l₁ (early-rf-at t ℓ {refl}) refl = {!!}
-- max≗⇓l₁ blurr-at refl = {!!}

-- max≗⇓r₂ (focl q lf ax refl) eqr refl =
--   congfoc (congfocl refl (congfocr (max≗rf eqr) refl))
-- max≗⇓r₂ (focl q lf (unfoc ok f) refl) eqr refl =
--   congfoc (congfocl refl (congfocr (max≗rf eqr) refl))
-- max≗⇓r₂ (unfoc ok f) eqr refl =
--   cong (λ x → only-rf⇑ _ _ _ x _) (max≗rf eqr)

-- max≗⇓rl₁ refl refl refl = refl
-- max≗⇓rl₁ (~ eq) refl refl = sym (max≗⇓rl₁ eq refl refl)
-- max≗⇓rl₁ (eq • eq₁) refl refl = trans (max≗⇓rl₁ eq refl refl) (max≗⇓rl₁ eq₁ refl refl)
-- max≗⇓rl₁ (unfoc eq) refl refl =
--   congfoc (congfocl refl (congfocr refl {!!}))
-- --   rewrite max≗⇑ eq = {!!}

-- max≗⇓rl₂ eql ax refl refl = congfoc (congfocl (max≗lf eql) refl)
-- max≗⇓rl₂ eql (unfoc ok f) refl refl = congfoc (congfocl (max≗lf eql) refl) 

-- max≗⇑ (⊸r {Γ = Γ} eq) = cong ⊸r (max≗⇑ {Γ = Γ ∷ʳ _} eq)
-- max≗⇑ (Il eq) = cong₂ Il (isProp-isPosAt _ _) (max≗⇑ eq)
-- max≗⇑ (⊗l eq) = cong₂ ⊗l (isProp-isPosAt _ _) (max≗⇑ eq)
-- max≗⇑ {S} (foc {s = s} {s'} {q} {q'} eq)
--   rewrite isProp-isIrr {S} s s' | isProp-isPosAt q q' = max≗⇓ eq

-- max≗⇓ refl = refl
-- max≗⇓ (~ eq) = sym (max≗⇓ eq)
-- max≗⇓ (eq • eq₁) = trans (max≗⇓ eq) (max≗⇓ eq₁)
-- max≗⇓ (focl eql {g = g} {eq = refl} {refl} eq) = 
--   trans (max≗⇓l₁ eq refl) (max≗⇓l₂ eql g refl)
-- max≗⇓ (focr eqr {g = g} {eq = refl}{refl} eq) =
--   trans (max≗⇓r₁ eq refl) (max≗⇓r₂ g eqr refl)
-- max≗⇓ (focrn eqr {refl , refl} {refl , refl} {eq = refl} {refl}) =
--   congfoc (congfocr (max≗rf eqr) refl)
-- max≗⇓ (swap {f = ax}) = refl
-- max≗⇓ (swap {f = unfoc ok f}) = refl

-- max≗⇓l₂ eql (focr (just (.(` _) , snd)) rf ax refl) refl =
--   congfoc (congfocl (max≗lf eql) refl) 
-- max≗⇓l₂ eql (focr (just x) rf (unfoc ok f) refl) refl =
--   congfoc (congfocl (max≗lf eql) refl) 
-- max≗⇓l₂ eql (unfoc ok f) refl =
--   cong (λ x → only-lf⇑ _ _ _ x (max f)) (max≗lf eql)

-- max≗⇓lr₁ refl refl refl = refl
-- max≗⇓lr₁ (~ eq) refl refl = sym (max≗⇓lr₁ eq refl refl)
-- max≗⇓lr₁ (eq • eq₁) refl refl = trans (max≗⇓lr₁ eq refl refl) (max≗⇓lr₁ eq₁ refl refl)
-- max≗⇓lr₁ (unfoc eq) refl refl = congfoc (congfocl refl (congfocr refl {!max≗⇑ eq!}))

-- max≗⇓lr₂ eqr ax refl refl = congfoc (congfocl refl (congfocr (max≗rf eqr) refl))
-- max≗⇓lr₂ eqr (unfoc ok f) refl refl = congfoc (congfocl refl (congfocr (max≗rf eqr) refl))


-- max≗lf blurl = refl
-- max≗lf (pass eq) = cong pass (max≗lf eq)
-- max≗lf (⊸l+ eqs eq {eq = refl}{refl}) =
--   cong₂ (⊸l+ _ _ _) (max≗⇑s eqs) (max≗lf eq)

-- max≗rf blurr = refl
-- max≗rf Ir = refl
-- max≗rf (⊗r+ eq eqs {refl} {refl}) = 
--   cong₂ (⊗r+ _ _ _) (max≗rf eq) (max≗⇑s eqs)

-- max≗⇑s [] = refl
-- max≗⇑s (eq ∷ eqs) = cong₂ _∷_ (max≗⇑ eq) (max≗⇑s eqs)

-- -- -- {-
-- -- -- max≗ (foc {S} {s = s} {s'} {q} {q'} refl)
-- -- --   rewrite isProp-isIrr {S} s s' | isProp-isPosAt q q' = refl
-- -- -- max≗ (foc (~ eq)) = sym (max≗ (foc eq))
-- -- -- max≗ (foc (eq • eq₁)) = {!!}
-- -- -- max≗ (foc (focl x eq)) = {!!}
-- -- -- max≗ (foc (focr x eq)) = {!!}
-- -- -- max≗ (foc (focrn x)) = {!!}
-- -- -- max≗ (foc swap) = {!!}
-- -- -- -}

-- -- -- {-
-- -- -- Il⇑eq : {Γ : Cxt} {Q : Fma} {q : isPosAt Q}
-- -- --         (f :  ─ ∣ Γ ⇑ Q) →
-- -- --   -------------------------
-- -- --        Il⇑ f ≡ Il q f
-- -- -- Il⇑eq {Q = ` x} (foc s q f) = refl
-- -- -- Il⇑eq {Q = I} (foc s q f) = refl
-- -- -- Il⇑eq {Q = Q ⊗ Q₁} (foc s q f) = refl

-- -- -- ⊗l⇑eq : {Γ : Cxt} {A B Q : Fma} {q : isPosAt Q}
-- -- --         (f :  just A ∣ B ∷ Γ ⇑ Q) →
-- -- --   -------------------------
-- -- --        ⊗l⇑ f ≡ ⊗l q f
-- -- -- ⊗l⇑eq {Q = ` x} (Il q f) = refl
-- -- -- ⊗l⇑eq {Q = ` x} (⊗l q f) = refl
-- -- -- ⊗l⇑eq {Q = ` x} (foc s q f) = refl
-- -- -- ⊗l⇑eq {Q = I} (Il q f) = refl
-- -- -- ⊗l⇑eq {Q = I} (⊗l q f) = refl
-- -- -- ⊗l⇑eq {Q = I} (foc s q f) = refl
-- -- -- ⊗l⇑eq {Q = Q ⊗ Q₁} (Il q f) = refl
-- -- -- ⊗l⇑eq {Q = Q ⊗ Q₁} (⊗l q f) = refl
-- -- -- ⊗l⇑eq {Q = Q ⊗ Q₁} (foc s q f) = refl

-- -- -- runLeq : ∀ {S Γ Δ A Q} {q : isPosAt Q}
-- -- --         {f :  S ∣ Γ ++ Δ ⇑ Q}
-- -- --         (ℓ : L S Γ A) →
-- -- --   -------------------------
-- -- --        runL {Δ = Δ} ℓ f ≡ runLQ q ℓ f
-- -- -- runLeq done = refl
-- -- -- runLeq (Il-1 ℓ) = trans (runLeq ℓ) (cong (runLQ _ ℓ) (Il⇑eq _))
-- -- -- runLeq (⊗l-1 ℓ) = trans (runLeq ℓ) (cong (runLQ _ ℓ) (⊗l⇑eq _))

-- -- -- ⊗r+Il⇑N : {Γ₀ Γ : Cxt} (Γ₁ Δ₀ : Cxt) {A B₀ : Fma}
-- -- --            (n : isNeg (Γ₁ ⊸⋆ A))
-- -- --            (Ξ : List (Cxt × Fma))
-- -- --            (f : ─ ∣ Γ ⇑ A)
-- -- --            (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ))
-- -- --            (eq : Γ ≡ Γ₀ ++ Γ₁) →
-- -- --            ⊗r+⇑N Γ₁ Δ₀ n Ξ (Il⇑ f) gs eq ≡ Il⇑ (⊗r+⇑N Γ₁ Δ₀ n Ξ f gs eq)
-- -- -- ⊗r+Il⇑N Γ₁ Δ₀ n Ξ (⊸r f) gs refl = ⊗r+Il⇑N (Γ₁ ∷ʳ _) Δ₀ n Ξ f gs refl
-- -- -- ⊗r+Il⇑N Γ₁ Δ₀ n Ξ (foc s q f) gs refl = refl

-- -- -- ⊗r+Il⇑ : {Γ : Cxt} (Δ₀ : Cxt) {B₀ A : Fma}
-- -- --           (Ξ : List (Cxt × Fma))
-- -- --           (f : ─ ∣ Γ ⇑ A)
-- -- --           (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)) →
-- -- --     ---------------------------------------------------------------------
-- -- --         ⊗r+⇑ Δ₀ Ξ (Il⇑ f) gs ≡ Il⇑ (⊗r+⇑ Δ₀ Ξ f gs)
-- -- -- ⊗r+Il⇑ Δ₀ {A = ` X} Ξ (foc s q f) gs = refl
-- -- -- ⊗r+Il⇑ Δ₀ {A = I} Ξ (foc s q f) gs = refl
-- -- -- ⊗r+Il⇑ Δ₀ {A = A' ⊗ B'} Ξ (foc s q f) gs = refl
-- -- -- ⊗r+Il⇑ Δ₀ {A = A' ⊸ B'} Ξ f gs = ⊗r+Il⇑N [] Δ₀ tt Ξ f gs refl

-- -- -- ⊗r+⊗l⇑N : {Γ₀ Γ : Cxt} (Γ₁ Δ₀ : Cxt) {A' B' A B₀ : Fma}
-- -- --            (n : isNeg (Γ₁ ⊸⋆ A))
-- -- --            (Ξ : List (Cxt × Fma))
-- -- --            (f : just A' ∣ B' ∷ Γ ⇑ A)
-- -- --            (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ))
-- -- --            (eq : Γ ≡ Γ₀ ++ Γ₁) →
-- -- --            ⊗r+⇑N Γ₁ Δ₀ n Ξ (⊗l⇑ f) gs eq ≡ ⊗l⇑ (⊗r+⇑N Γ₁ Δ₀ n Ξ f gs (cong (B' ∷_) eq))
-- -- -- ⊗r+⊗l⇑N Γ₁ Δ₀ n Ξ (⊸r f) gs refl = ⊗r+⊗l⇑N (Γ₁ ∷ʳ _) Δ₀ n Ξ f gs refl
-- -- -- ⊗r+⊗l⇑N Γ₁ Δ₀ n Ξ (Il q f) gs refl = refl
-- -- -- ⊗r+⊗l⇑N Γ₁ Δ₀ n Ξ (⊗l q f) gs refl =  refl
-- -- -- ⊗r+⊗l⇑N Γ₁ Δ₀ {` X} n Ξ (foc s q f) gs refl = refl
-- -- -- ⊗r+⊗l⇑N Γ₁ Δ₀ {_ ⊸ _} n Ξ (foc s q f) gs refl = refl

-- -- -- ⊗r+⊗l⇑ : {Γ : Cxt} (Δ₀ : Cxt) {A' B' B₀ A : Fma}
-- -- --           (Ξ : List (Cxt × Fma))
-- -- --           (f : just A' ∣ B' ∷ Γ ⇑ A)
-- -- --           (gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)) →
-- -- --     ---------------------------------------------------------------------
-- -- --         ⊗r+⇑ Δ₀ Ξ (⊗l⇑ f) gs ≡ ⊗l⇑ (⊗r+⇑ Δ₀ Ξ f gs)
-- -- -- ⊗r+⊗l⇑ Δ₀ {A = ` X} Ξ (Il q f) gs = refl
-- -- -- ⊗r+⊗l⇑ Δ₀ {A = ` X} Ξ (⊗l q f) gs = refl
-- -- -- ⊗r+⊗l⇑ Δ₀ {A = ` X} Ξ (foc s q f) gs = refl
-- -- -- ⊗r+⊗l⇑ Δ₀ {A = I} Ξ (Il q f) gs = refl
-- -- -- ⊗r+⊗l⇑ Δ₀ {A = I} Ξ (⊗l q f) gs = refl
-- -- -- ⊗r+⊗l⇑ Δ₀ {A = I} Ξ (foc s q f) gs = refl
-- -- -- ⊗r+⊗l⇑ Δ₀ {A = A' ⊗ B'} Ξ (Il q f) gs = refl
-- -- -- ⊗r+⊗l⇑ Δ₀ {A = A' ⊗ B'} Ξ (⊗l q f) gs = refl
-- -- -- ⊗r+⊗l⇑ Δ₀ {A = A' ⊗ B'} Ξ (foc s q f) gs = refl
-- -- -- ⊗r+⊗l⇑ Δ₀ {A = A' ⊸ B'} Ξ f gs = ⊗r+⊗l⇑N [] Δ₀ tt Ξ f gs refl

-- -- -- ⊸r⊸l⇑ : {Γ Δ : Cxt} {A B C D : Fma}
-- -- --          (f : ─ ∣ Γ ⇑ A) (g : just B ∣ Δ ∷ʳ D ⇑ C) → 
-- -- --     -----------------------------------------------------------------------
-- -- --         ⊸r (⊸l⇑ f g) ≡ ⊸l⇑ f (⊸r g)
-- -- -- ⊸r⊸l⇑ {B = ` X} f g = refl
-- -- -- ⊸r⊸l⇑ {B = I} f g = refl
-- -- -- ⊸r⊸l⇑ {B = B ⊗ B₁} f g = refl
-- -- -- ⊸r⊸l⇑ {B = B ⊸ B₁} f g = refl

-- -- -- ⊸r⋆⊸r⋆⇑ : {S : Stp} {Γ : Cxt} (Δ : Cxt) {Δ' : Cxt} {A : Fma}
-- -- --          {f : S ∣ Γ ++ Δ ++ Δ' ⇑ A} →
-- -- --          ⊸r⋆⇑ (Δ ++ Δ') f ≡ ⊸r⋆⇑ Δ (⊸r⋆⇑ {Γ = Γ ++ Δ} Δ' f)
-- -- -- ⊸r⋆⊸r⋆⇑ [] = refl
-- -- -- ⊸r⋆⊸r⋆⇑ (_ ∷ Δ) {Δ'} = cong ⊸r (⊸r⋆⊸r⋆⇑ Δ {Δ'})

-- -- -- ⊸r⋆Il⇑ : {Γ : Cxt} (Δ : Cxt) {A : Fma}
-- -- --          {f : ─ ∣ Γ ++ Δ ⇑ A} →
-- -- --          ⊸r⋆⇑ Δ (Il⇑ f) ≡ Il⇑ (⊸r⋆⇑ Δ f)
-- -- -- ⊸r⋆Il⇑ [] = refl
-- -- -- ⊸r⋆Il⇑ (_ ∷ Δ) = cong ⊸r (⊸r⋆Il⇑ Δ)

-- -- -- ⊸r⋆⊗l⇑ : {Γ : Cxt} (Δ : Cxt) {A A' B' : Fma}
-- -- --          {f : just A' ∣ B' ∷ Γ ++ Δ ⇑ A} →
-- -- --          ⊸r⋆⇑ Δ (⊗l⇑ f) ≡ ⊗l⇑ (⊸r⋆⇑ Δ f)
-- -- -- ⊸r⋆⊗l⇑ [] = refl
-- -- -- ⊸r⋆⊗l⇑ (_ ∷ Δ) = cong ⊸r (⊸r⋆⊗l⇑ Δ)

-- -- -- ⊸r⋆runL : ∀ {S Γ₀ Γ₁} Δ {A Q} 
-- -- --          {f : S ∣ Γ₀ ++ Γ₁ ++ Δ ⇑ Q}
-- -- --          (ℓ : L S Γ₀ A) →
-- -- --          ⊸r⋆⇑ Δ (runL {Δ = Γ₁ ++ Δ} ℓ f) ≡ runL {Δ = Γ₁} ℓ (⊸r⋆⇑ Δ f)
-- -- -- ⊸r⋆runL Δ done = refl
-- -- -- ⊸r⋆runL Δ (Il-1 ℓ) = trans (⊸r⋆runL Δ ℓ) (cong (runL ℓ) (⊸r⋆Il⇑ Δ)) 
-- -- -- ⊸r⋆runL Δ (⊗l-1 ℓ) = trans (⊸r⋆runL Δ ℓ) (cong (runL ℓ) (⊸r⋆⊗l⇑ Δ)) 

-- -- -- congIl⇑ : ∀{Γ C} {f g : ─ ∣ Γ ⇑ C} → f ≗⇑ g → Il⇑ f ≗⇑ Il⇑ g
-- -- -- congIl⇑ refl = refl
-- -- -- congIl⇑ (~ eq) = ~ congIl⇑ eq
-- -- -- congIl⇑ (eq • eq₁) = congIl⇑ eq • congIl⇑ eq₁
-- -- -- congIl⇑ (⊸r eq) = ⊸r (congIl⇑ eq)
-- -- -- congIl⇑ (foc eq) = Il (foc eq)

-- -- -- cong⊗l⇑ : ∀{Γ A B C} {f g : just A ∣ B ∷ Γ ⇑ C} → f ≗⇑ g → ⊗l⇑ f ≗⇑ ⊗l⇑ g
-- -- -- cong⊗l⇑ refl = refl
-- -- -- cong⊗l⇑ (~ eq) = ~ cong⊗l⇑ eq
-- -- -- cong⊗l⇑ (eq • eq₁) = cong⊗l⇑ eq • cong⊗l⇑ eq₁
-- -- -- cong⊗l⇑ (⊸r eq) = ⊸r (cong⊗l⇑ eq)
-- -- -- cong⊗l⇑ (Il eq) = ⊗l (Il eq)
-- -- -- cong⊗l⇑ (⊗l eq) = ⊗l (⊗l eq)
-- -- -- cong⊗l⇑ (foc eq) = ⊗l (foc eq) 

-- -- -- cong⊸r⋆⇑ : {S : Stp} {Γ : Cxt} (Δ : Cxt) {A : Fma}
-- -- --            {f g : S ∣ Γ ++ Δ ⇑ A} → f ≗⇑ g → 
-- -- --            ⊸r⋆⇑ Δ f ≗⇑ ⊸r⋆⇑ Δ g
-- -- -- cong⊸r⋆⇑ [] eq = eq
-- -- -- cong⊸r⋆⇑ (_ ∷ Δ) eq = ⊸r (cong⊸r⋆⇑ Δ eq)

-- -- -- congrunL : ∀{S Γ Δ A C} {f g : S ∣ Γ ++ Δ ⇑ C} (ℓ : L S Γ A)→ f ≗⇑ g
-- -- --   → runL {Δ = Δ} ℓ f ≗⇑ runL ℓ g
-- -- -- congrunL done eq = eq
-- -- -- congrunL (Il-1 ℓ) eq = congrunL ℓ (congIl⇑ eq)
-- -- -- congrunL (⊗l-1 ℓ) eq = congrunL ℓ (cong⊗l⇑ eq)

-- -- -- congrunLQ : ∀{S Γ Δ A C q q'} {f g : S ∣ Γ ++ Δ ⇑ C} (ℓ : L S Γ A)→ f ≗⇑ g
-- -- --   → runLQ {Δ = Δ} q ℓ f ≗⇑ runLQ q' ℓ g
-- -- -- congrunLQ done eq = eq
-- -- -- congrunLQ (Il-1 ℓ) eq = congrunLQ ℓ (Il eq)
-- -- -- congrunLQ (⊗l-1 ℓ) eq = congrunLQ ℓ (⊗l eq)

-- -- -- swap' : ∀ {S Γ Γ₀ Γ₁ Γ₂ C M Q q m}
-- -- --          {lf : q ⇛lf S ； Γ₀} {rf : just (M , m) ⇛rf Γ₂ ； C}
-- -- --          {f : [ ∙ , ∙ ] just Q ∣ Γ₁ ⇓ M}
-- -- --          (eq : Γ ≡ Γ₀ ++ Γ₁) {eq' : Γ ++ Γ₂ ≡ Γ₀ ++ Γ₁ ++ Γ₂} →
-- -- --          focl q lf (focr _ rf f refl) eq' ≗⇓ focr _ rf (focl q lf f eq) refl
-- -- -- swap' refl {refl} = swap

-- -- -- swap'' : ∀ {S Γ Γ₀ Γ₁ Γ₂ C M Q q m}
-- -- --          {lf : q ⇛lf S ； Γ₀} {rf : just (M , m) ⇛rf Γ₂ ； C}
-- -- --          {f : [ ∙ , ∙ ] just Q ∣ Γ₁ ⇓ M}
-- -- --          (eq : Γ ≡ Γ₁ ++ Γ₂) {eq' : Γ₀ ++ Γ ≡ Γ₀ ++ Γ₁ ++ Γ₂} →
-- -- --          focl q lf (focr _ rf f eq) refl ≗⇓ focr _ rf (focl q lf f refl) eq'
-- -- -- swap'' refl {refl} = swap

-- -- -- early-pass⇓-at : ∀ {Γ₀} Δ {X Q n q}
-- -- --   → (x : isAt X)
-- -- --   → (f : [ ∘ , ∘ ] just X ∣ Γ₀ ++ Δ ⇓ Q)
-- -- --   → unfoc {∘}{∙} n (⊸r⋆⇑ Δ (foc tt q (pass⇓ f)))
-- -- --           ≗⇓ focl (at→posat x) (pass blurl) (unfoc (inj₂ n) (⊸r⋆⇑ Δ (foc (at→negat x) q f))) refl

-- -- -- early-pass⇑-at : ∀ {Γ₀} Δ {X A n}
-- -- --   → (x : isAt X)
-- -- --   → (f : just X ∣ Γ₀ ++ Δ ⇑ A)
-- -- --   → unfoc {∘}{∙} n (⊸r⋆⇑ Δ (pass⇑ f)) ≗⇓ focl (at→posat x) (pass blurl) (unfoc (inj₂ n) (⊸r⋆⇑ Δ f)) refl

-- -- -- early-pass⇑-at {Γ₀} Δ x (⊸r f) =
-- -- --   unfoc-same (~ (refl⇑ (⊸r⋆⊸r⋆⇑ Δ {_ ∷ []})))
-- -- --   • early-pass⇑-at {Γ₀} (Δ ∷ʳ _) x f
-- -- --   • focl refl (unfoc (refl⇑ (⊸r⋆⊸r⋆⇑ Δ {_ ∷ []})))
-- -- -- early-pass⇑-at Δ {` X} x (foc s q f) = early-pass⇓-at Δ tt f

-- -- -- early-pass⇓-at Δ {` X} {q = q} x (focr (just (M , m)) rf (focl _ blurl f refl) eq) =
-- -- --   unfoc-same (cong⊸r⋆⇑ Δ (foc-same (~ swap'' eq)))
-- -- --   • early-lf-at Δ q {eq = refl}
-- -- --   • focl refl (unfoc (cong⊸r⋆⇑ Δ (foc-same (swap'' eq))))
-- -- -- early-pass⇓-at Δ {` X} {q = q} x (focr (just (M , m)) rf (unfoc ok f) eq) = 
-- -- --   unfoc-same (cong⊸r⋆⇑ Δ (foc-same (focr refl {eq' = cong (_ ∷_) eq} (early-pass⇑-at [] tt f) • ~ (swap'' eq))))
-- -- --   • early-lf-at Δ q {eq = refl}
-- -- --   • focl refl (unfoc (cong⊸r⋆⇑ Δ (foc-same (swap'' eq {eq} • focr refl blurl-at))))

-- -- -- early-pass⇓-at Δ {` X} {q = q} x (focl _ blurl f refl) = early-lf-at Δ q



-- -- -- {-
-- -- -- early-rf' : ∀ {T Γ₀ Γ₁ Γ₂ Γ} Γ' {Δ P Q Q' R} t {n : isNegAt (Γ' ⊸⋆ Q)} {p : isPos P} {q : isPosAt Q} {q' : isPos Q'} {r}
-- -- --             {lf : pos→posat q' ⇛lf T ； Γ₀} {rf : just (Γ' ⊸⋆ Q , n) ⇛rf Γ₂ ； R}
-- -- --             {f : just Q' ∣ Γ ++ Γ' ⇑ Q} (ℓ : L T Δ P) →
-- -- --             (eq : Δ ++ Γ₁ ≡ Γ₀ ++ Γ) → 
-- -- --             unfoc {∙}{∘} p (runL {Δ = Γ₁ ++ Γ₂} ℓ (foc t r (focr {∘} {Γ₀ = Δ ++ Γ₁}{Γ₂} _ rf (focl {Γ₀ = Γ₀}{Γ} _ lf (unfoc (inj₁ q') (⊸r⋆⇑ Γ' f)) eq) refl)))
-- -- --               ≗⇓ focr {Γ₀ = Γ₁} {Γ₂} _ rf (unfoc (inj₁ p) (⊸r⋆⇑ Γ' (runL {Δ = Γ₁ ++ Γ'} ℓ (foc t q (focl {Γ₀ = Γ₀} {Γ ++ Γ'} _ lf (unfoc q' f) (cong (_++ Γ') {x = Δ ++ Γ₁}{Γ₀ ++ Γ} eq)))))) refl

-- -- -- early-rf' Γ' t {q = q} ℓ eq =
-- -- --   unfoc (congrunL ℓ (foc-same (focr refl (~ (early-lf Γ' q)))))
-- -- --   • {!!}

-- -- -- early-lf' : ∀ {S' S Γ₀ Γ₁ Γ₂ Γ Γ'} Δ {M Q R} {s : isIrr S} {s' : isIrr S'} {m : isNeg M} {n : isNeg (Δ ⊸⋆ R)} {q : isPos Q} (r : isPosAt R)
-- -- --      {lf : pos→posat q ⇛lf S ； Γ₀} {rf : just (M , neg→negat m) ⇛rf Γ₂ ； R} 
-- -- --      {f : S' ∣ Γ' ++ Γ ⇑ M} →  --Γ₁ ++ Δ
-- -- --      (eq : Γ₁ ++ Δ ≡ Γ ++ Γ₂)
-- -- --      (ℓ : L S' Γ' Q) → 
-- -- --      _≗⇓_ {∘}{∙} {Γ = Γ₀ ++ Γ₁}
-- -- --         (unfoc {∘}{∙} n (⊸r⋆⇑ Δ (foc s r (focl {∘}{Γ₀ = Γ₀}{Γ₁ ++ Δ} (pos→posat q) lf (focr {Γ₀ = Γ} {Γ₂} _ rf (unfoc (inj₁ q) (runL {Δ = Γ} ℓ f)) eq) refl))))
-- -- --         (focl {∙} {Γ₀ = Γ₀}{Γ₁}  _ lf (unfoc {∙}{∙} (inj₁ q) (⊸r⋆⇑ Δ (runL {Δ = Γ₁ ++ Δ} ℓ (foc s' r (focr {Γ₀ = Γ' ++ Γ} _ rf (unfoc m f) (cong (Γ' ++_) eq)))))) refl)
-- -- -- early-lf' Δ r eq ℓ =
-- -- --   unfoc (cong⊸r⋆⇑ Δ (foc-same (focl refl (~ (early-rf _ ℓ)))))
-- -- --   • early-lf Δ r
-- -- -- -}


-- -- -- pass⊸r⋆⇑ : {Γ : Cxt} (Δ : Cxt) {A C : Fma}
-- -- --            {f : just A ∣ Γ ++ Δ ⇑ C} →
-- -- --   --------------------------------------------
-- -- --         pass⇑ (⊸r⋆⇑ Δ f) ≡ ⊸r⋆⇑ Δ (pass⇑ f)
-- -- -- pass⊸r⋆⇑ [] = refl
-- -- -- pass⊸r⋆⇑ {Γ} (B ∷ Δ) = cong ⊸r (pass⊸r⋆⇑ {Γ ∷ʳ B} Δ)

-- -- -- congpass⇑ : ∀ {Γ A C} {f g : just A ∣ Γ ⇑ C} → f ≗⇑ g
-- -- --   → pass⇑ f ≗⇑ pass⇑ g
-- -- -- congpass⇓ : ∀ {b Γ A C} {f g : [ ∘ , b ] just A ∣ Γ ⇓ C} → f ≗⇓ g
-- -- --   → pass⇓ f ≗⇓ pass⇓ g

-- -- -- congpass⇑ refl = refl
-- -- -- congpass⇑ (~ eq) = ~ congpass⇑ eq
-- -- -- congpass⇑ (eq • eq₁) = congpass⇑ eq • congpass⇑ eq₁
-- -- -- congpass⇑ (⊸r eq) = ⊸r (congpass⇑ eq)
-- -- -- congpass⇑ (Il eq) = foc (focl refl (unfoc (Il eq)))
-- -- -- congpass⇑ (⊗l eq) = foc (focl refl (unfoc (⊗l eq)))
-- -- -- congpass⇑ (foc eq) = foc (congpass⇓ eq)

-- -- -- congpass⇓ refl = refl
-- -- -- congpass⇓ (~ eq) = ~ congpass⇓ eq
-- -- -- congpass⇓ (eq • eq₁) = congpass⇓ eq • congpass⇓ eq₁
-- -- -- congpass⇓ (focl eql eq) = focl (pass eql) eq
-- -- -- congpass⇓ (focr eqr eq) = focr eqr (congpass⇓ eq)
-- -- -- congpass⇓ {∙} (unfoc eq) = unfoc (congpass⇑ eq)
-- -- -- congpass⇓ swap = swap
-- -- -- congpass⇓ (early-lf Δ r {eq = refl}) = unfoc-same (refl⇑ (pass⊸r⋆⇑ Δ)) • early-lf Δ r
-- -- -- congpass⇓ (early-lf-at Δ r {eq = refl}) = unfoc (refl⇑ (pass⊸r⋆⇑ Δ)) • early-lf-at Δ r
-- -- -- congpass⇓ (blurl-at {f = f}) = ~ early-pass⇑-at [] tt f

-- -- -- Il⊗r+⇑Q : {Γ Δ₀ : Cxt} {B₀ Q : Fma}
-- -- --           {q : isPosAt Q}
-- -- --           {Ξ : List (Cxt × Fma)}
-- -- --           (f : ─ ∣ Γ ⇑ Q)
-- -- --           {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} →
-- -- --           ⊗r+⇑Q Δ₀ q Ξ (Il⇑ f) gs ≡ Il⇑ (⊗r+⇑Q Δ₀ q Ξ f gs)
-- -- -- Il⊗r+⇑Q (foc s q f) = refl

-- -- -- ⊗l⊗r+⇑Q : {Γ Δ₀ : Cxt} {A B B₀ Q : Fma}
-- -- --           {q : isPosAt Q}
-- -- --           {Ξ : List (Cxt × Fma)}
-- -- --           (f : just A ∣ B ∷ Γ ⇑ Q)
-- -- --           {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} →
-- -- --           ⊗r+⇑Q Δ₀ q Ξ (⊗l⇑ f) gs ≡ ⊗l⇑ (⊗r+⇑Q Δ₀ q Ξ f gs)
-- -- -- ⊗l⊗r+⇑Q (Il q f) = refl
-- -- -- ⊗l⊗r+⇑Q (⊗l q f) = refl
-- -- -- ⊗l⊗r+⇑Q (foc s q f) = refl

-- -- -- runL⊗r+⇑Q : {S : Stp} {Γ Δ Δ₀ : Cxt} {B₀ Q A : Fma}
-- -- --             {q : isPosAt Q}
-- -- --             {Ξ : List (Cxt × Fma)}
-- -- --             {f : S ∣ Γ ++ Δ ⇑ Q}
-- -- --             {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)}
-- -- --             (ℓ : L S Γ A) → 
-- -- --     ---------------------------------------------------------------------
-- -- --         ⊗r+⇑Q Δ₀ q Ξ (runL {Δ = Δ} ℓ f) gs ≡
-- -- --           runL {Δ = Δ ++ Δ₀ ++ concat (cxts Ξ)} ℓ (⊗r+⇑Q Δ₀ q Ξ f gs)

-- -- -- runL⊗r+⇑Q done = refl
-- -- -- runL⊗r+⇑Q (Il-1 ℓ) = trans (runL⊗r+⇑Q ℓ) (cong (runL ℓ) (Il⊗r+⇑Q _))
-- -- -- runL⊗r+⇑Q (⊗l-1 ℓ) = trans (runL⊗r+⇑Q ℓ) (cong (runL ℓ) (⊗l⊗r+⇑Q _))

-- -- -- runLQ⊗r+⇑Q : {S : Stp} {Γ Δ Δ₀ : Cxt} {B₀ Q A : Fma}
-- -- --             {q q' : isPosAt Q}
-- -- --             {Ξ : List (Cxt × Fma)}
-- -- --             {f : S ∣ Γ ++ Δ ⇑ Q}
-- -- --             {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)}
-- -- --             (ℓ : L S Γ A) → 
-- -- --     ---------------------------------------------------------------------
-- -- --         ⊗r+⇑Q Δ₀ q Ξ (runLQ {Δ = Δ} q' ℓ f) gs ≡
-- -- --           runLQ {Δ = Δ ++ Δ₀ ++ concat (cxts Ξ)} (isPosAt⊗⋆ tt (fmas Ξ)) ℓ (⊗r+⇑Q Δ₀ q Ξ f gs)

-- -- -- runLQ⊗r+⇑Q done = refl
-- -- -- runLQ⊗r+⇑Q (Il-1 ℓ) = runLQ⊗r+⇑Q ℓ
-- -- -- runLQ⊗r+⇑Q (⊗l-1 ℓ) = runLQ⊗r+⇑Q ℓ

-- -- -- cong⊗r+⇓Q₁ : ∀ {b S Γ Δ₀ B₀ Q q Ξ}
-- -- --             {f f' : [ b , ∘ ] S ∣ Γ ⇓ Q} (eq : f ≗⇓ f') 
-- -- --             {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} →  
-- -- --     ---------------------------------------------------------------------
-- -- --            ⊗r+⇓Q Δ₀ q Ξ f gs ≗⇓ ⊗r+⇓Q Δ₀ q Ξ f' gs

-- -- -- refls⇑ : ∀ {Ξ} {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ} → fs ≗s⇑ fs
-- -- -- refls⇑ {fs = []} = []
-- -- -- refls⇑ {fs = f ∷ fs} = refl ∷ refls⇑

-- -- -- ++≗s₁ : ∀ {Ξ Ξ'} {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ}
-- -- --   → fs ≗s⇑ gs
-- -- --   → {hs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ'}
-- -- --   → (fs ++All hs) ≗s⇑ (gs ++All hs)
-- -- -- ++≗s₁ [] = refls⇑ 
-- -- -- ++≗s₁ (eq ∷ eqs) = eq ∷ (++≗s₁ eqs)

-- -- -- ++≗s₂ : ∀ {Ξ Ξ'} (fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ)
-- -- --   → {gs hs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ'}
-- -- --   →  gs ≗s⇑ hs
-- -- --   → (fs ++All gs) ≗s⇑ (fs ++All hs)
-- -- -- ++≗s₂ [] eqs = eqs
-- -- -- ++≗s₂ (f ∷ fs) eqs = refl ∷ (++≗s₂ fs eqs)

-- -- -- ++rf≗₁ : ∀ {Δ₀ Γ B₀ C Ξ s}
-- -- --        {h k : s ⇛rf Γ ； C} → h ≗rf k → 
-- -- --        {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} →
-- -- --         ++rf Δ₀ Ξ s h gs ≗rf ++rf Δ₀ Ξ s k gs
-- -- -- ++rf≗₁ refl = refl
-- -- -- ++rf≗₁ (~ eq) = ~ (++rf≗₁ eq)
-- -- -- ++rf≗₁ (eq • eq₁) = (++rf≗₁ eq) • (++rf≗₁ eq₁)
-- -- -- ++rf≗₁ (⊗r+ eq eqs) = ⊗r+ eq (++≗s₁ eqs)

-- -- -- ++rf≗₂ : ∀ {Δ₀ Γ B₀ C Ξ s}
-- -- --          (h : s ⇛rf Γ ； C) → 
-- -- --          {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → fs ≗s⇑ gs → 
-- -- --          ++rf Δ₀ Ξ s h fs ≗rf ++rf Δ₀ Ξ s h gs
-- -- -- ++rf≗₂ Ir eqs = ⊗r+ refl eqs
-- -- -- ++rf≗₂ (⊗r+ Δ₀ Ξ m h gs eq) eqs = ⊗r+ refl (++≗s₂ gs eqs)
-- -- -- ++rf≗₂ blurr eqs = ⊗r+ refl eqs

-- -- -- ++lf≗₁ : ∀ {Γ₀ Γ Q A₀ M Ξ} {q : isPosAt Q}
-- -- --          {h k : q ⇛lf just M ； Γ} → h ≗lf k → 
-- -- --          {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)} →
-- -- --          ++lf Γ₀ Ξ q h gs ≗lf ++lf Γ₀ Ξ q k gs
-- -- -- ++lf≗₁ refl = refl
-- -- -- ++lf≗₁ (~ eq) = ~ (++lf≗₁ eq)
-- -- -- ++lf≗₁ (eq • eq₁) = ++lf≗₁ eq • ++lf≗₁ eq₁
-- -- -- ++lf≗₁ (⊸l+ eql eq {refl}{refl}) = ⊸l+ (++≗s₂ _ eql) eq

-- -- -- ++lf≗₂ : ∀ {Γ₀ Γ Q A₀ M Ξ} {q : isPosAt Q}
-- -- --          (h : q ⇛lf just M ； Γ)
-- -- --          {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)} → fs ≗s⇑ gs → 
-- -- --          ++lf Γ₀ Ξ q h fs ≗lf ++lf Γ₀ Ξ q h gs
-- -- -- ++lf≗₂ (⊸l+ Γ₀ Ξ q fs h refl) eqs = ⊸l+ (++≗s₁ eqs) refl
-- -- -- ++lf≗₂ blurl eqs = ⊸l+ eqs refl


-- -- -- early-rf⇓-at : ∀ {S Γ₀ Δ Δ₀ X P B₀ p s Ξ}
-- -- --   → (x : isAt X)
-- -- --   → (f : [ ∘ , ∘ ] S ∣ Δ ++ Γ₀ ⇓ X)
-- -- --   → {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)}
-- -- --   → (ℓ : L S Δ P)
-- -- --   → unfoc {∙}{∘} p (runL {Δ = Γ₀ ++ Δ₀ ++ concat (cxts Ξ)} ℓ (foc s (isPosAt⊗⋆ tt (fmas Ξ)) (⊗r+⇓Q Δ₀ (at→posat x) Ξ f gs)))
-- -- --          ≗⇓ focr {Γ₀ = Γ₀} (just (_ , at→negat x)) (⊗r+ Δ₀ Ξ (negat→isn't⊗ (at→negat x)) blurr gs refl) (unfoc (inj₁ p) (runL {Δ = Γ₀} ℓ (foc s (at→posat x) f))) refl


-- -- -- early-rf⇑-at : ∀ {S Γ₀ Δ Γ Δ₀ X P B₀ p Ξ}
-- -- --   → (x : isAt X)
-- -- --   → (f : S ∣ Γ ⇑ X)
-- -- --   → {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)}
-- -- --   → (eq : Γ ≡ Δ ++ Γ₀)
-- -- --   → (ℓ : L S Δ P)
-- -- --   → unfoc {∙}{∘} p (runL {Δ = Γ₀ ++ Δ₀ ++ concat (cxts Ξ)} ℓ (⊗r+⇑Q Δ₀ (at→posat x) Ξ (subst⇑ f eq) gs))
-- -- --          ≗⇓ focr {Γ₀ = Γ₀} (just (_ , at→negat x)) (⊗r+ Δ₀ Ξ (negat→isn't⊗ (at→negat x)) blurr gs refl) (unfoc (inj₁ p) (runL {Δ = Γ₀} ℓ (subst⇑ f eq))) refl

-- -- -- early-rf⇑-at x (Il q f) refl ℓ =
-- -- --   unfoc-same (refl⇑ (cong (runL ℓ) (sym (Il⇑eq _))))
-- -- --   • early-rf⇑-at x f refl (Il-1 ℓ)
-- -- --   • focr refl (unfoc (refl⇑ (cong (runL ℓ) (Il⇑eq _))))
-- -- -- early-rf⇑-at x (⊗l q f) refl ℓ = 
-- -- --   unfoc-same (refl⇑ (cong (runL ℓ) (sym (⊗l⇑eq _))))
-- -- --   • early-rf⇑-at x f refl (⊗l-1 ℓ)
-- -- --   • focr refl (unfoc (refl⇑ (cong (runL ℓ) (⊗l⇑eq _))))
-- -- -- early-rf⇑-at {X = ` X} x (foc s q f) refl ℓ = early-rf⇓-at x f ℓ

-- -- -- early-rf⇓-at x (focl q lf (focr (just _) (⊗r+ Δ₀ Ξ m rf gs eq₁) ax refl) eq) ℓ = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))
-- -- -- early-rf⇓-at x (focl q lf (focr (just (M , m)) (⊗r+ Δ₀ Ξ m₁ rf gs eq₂) (unfoc ok f) eq₁) eq) ℓ = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))
-- -- -- early-rf⇓-at {p = p} {s = s} {Ξ} x (focl {Q} q lf (focr (just (` X , tt)) blurr f refl) eq) ℓ = 
-- -- --   unfoc-same (congrunL ℓ (foc-same (swap' eq)))
-- -- --   • early-rf-at s ℓ
-- -- --   • focr refl (unfoc (congrunL ℓ (foc (~ swap' eq))))
-- -- -- early-rf⇓-at {Δ₀ = Δ₀} {X = ` X} {s = s} {Ξ} x (focl q lf (unfoc ok f) eq) ℓ = 
-- -- --   unfoc-same (congrunL ℓ (foc-same (focl refl {eq' = cong (λ a → a ++ Δ₀ ++ concat (cxts Ξ)) eq} (early-rf⇑-at tt f refl done) • swap' eq)))
-- -- --   • early-rf-at s ℓ
-- -- --   • focr refl (unfoc (congrunL ℓ (foc-same (~ swap' eq {eq} • focl refl blurr-at))))

-- -- -- early-rf⇓-at x (focr ─ (⊗r+ Δ₀ Ξ m rf gs eq₁) f eq) ℓ = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))
-- -- -- early-rf⇓-at x (focr (just (M , m)) (⊗r+ Δ₀ Ξ m₁ rf' gs eq₁) f eq) ℓ = ⊥-elim (pos×negat→⊥ (isPos⊗⋆ tt (fmas Ξ)) (at→negat x))
-- -- -- early-rf⇓-at {s = s} x (focr (just (` X , _)) blurr f refl) ℓ = early-rf-at s ℓ




-- -- -- early-rf⇑N : ∀ {S Γ₀ Δ Γ Γ₁ Δ₀ A P B₀ n p Ξ}
-- -- --  → (f : S ∣ Γ ⇑ A)
-- -- --  → {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)}
-- -- --  → {eq : Γ ≡ Δ ++ Γ₀ ++ Γ₁}
-- -- --  → (ℓ : L S Δ P)
-- -- --  → unfoc {∙}{∘} p (runL {Δ = Γ₀ ++ Δ₀ ++ concat (cxts Ξ)} ℓ (⊗r+⇑N {Γ₀ = Δ ++ Γ₀} Γ₁ Δ₀ n Ξ f gs eq))
-- -- --          ≗⇓ focr {Γ₀ = Γ₀} (just (_ , neg→negat n)) (⊗r+ Δ₀ Ξ (neg→isn't⊗ n) blurr gs refl) (unfoc (inj₁ p) (runL {Δ = Γ₀} ℓ (⊸r⋆⇑ Γ₁ (subst⇑ f eq)))) refl
-- -- -- early-rf⇑N {Γ₁ = Γ₁} (⊸r f) {eq = refl} ℓ =
-- -- --   early-rf⇑N f ℓ • focr refl (unfoc (refl⇑ (cong (runL ℓ) (⊸r⋆⊸r⋆⇑ Γ₁ {_ ∷ []}))))
-- -- -- early-rf⇑N {Γ₁ = Γ₁} (Il q f) {eq = refl} ℓ =
-- -- --   unfoc-same (refl⇑ (cong (runL ℓ) (sym (Il⇑eq _))))
-- -- --   • early-rf⇑N f (Il-1 ℓ)
-- -- --   • focr refl (unfoc (refl⇑ (cong (runL ℓ) (trans (sym (⊸r⋆Il⇑ Γ₁)) (cong (⊸r⋆⇑ Γ₁) (Il⇑eq f))))))
-- -- -- early-rf⇑N {Γ₁ = Γ₁} (⊗l q f) {eq = refl} ℓ =
-- -- --   unfoc-same (refl⇑ (cong (runL ℓ) (sym (⊗l⇑eq _))))
-- -- --   • early-rf⇑N f (⊗l-1 ℓ)
-- -- --   • focr refl (unfoc (refl⇑ (cong (runL ℓ) (trans (sym (⊸r⋆⊗l⇑ Γ₁)) (cong (⊸r⋆⇑ Γ₁) (⊗l⇑eq f))))))
-- -- -- early-rf⇑N (foc s q f) {eq = refl} ℓ = early-rf s ℓ 

-- -- -- cong⊗r+⇑Q₁ : ∀ {S Γ Δ₀ B₀ Q q Ξ}
-- -- --              {f f' : S ∣ Γ ⇑ Q} → f ≗⇑ f' →
-- -- --              {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → 
-- -- --        ---------------------------------------------------------------------
-- -- --            ⊗r+⇑Q Δ₀ q Ξ f gs ≗⇑ ⊗r+⇑Q Δ₀ q Ξ f' gs

-- -- -- cong⊗r+⇓Q₁ refl = refl
-- -- -- cong⊗r+⇓Q₁ (~ eq) = ~ (cong⊗r+⇓Q₁ eq)
-- -- -- cong⊗r+⇓Q₁ (eq • eq₁) = (cong⊗r+⇓Q₁ eq) • (cong⊗r+⇓Q₁ eq₁)
-- -- -- cong⊗r+⇓Q₁ (focl eql eq) = focl eql (cong⊗r+⇓Q₁ eq)
-- -- -- cong⊗r+⇓Q₁ (focr eqr eq) = focr (++rf≗₁ eqr) eq
-- -- -- cong⊗r+⇓Q₁ (focrn eqr) = focrn (++rf≗₁ eqr)
-- -- -- cong⊗r+⇓Q₁ {∙} {just P} (unfoc eq) = unfoc (cong⊗r+⇑Q₁ eq)
-- -- -- cong⊗r+⇓Q₁ swap = swap
-- -- -- cong⊗r+⇓Q₁ (early-rf t ℓ {eq = refl}) = unfoc (refl⇑ (runL⊗r+⇑Q ℓ)) • early-rf t ℓ
-- -- -- cong⊗r+⇓Q₁ (early-rf-at t ℓ {eq = refl}) = unfoc (refl⇑ (runL⊗r+⇑Q ℓ)) • early-rf-at t ℓ
-- -- -- cong⊗r+⇓Q₁ (blurr-at {f = f}) = ~ early-rf⇑-at tt f refl done


-- -- -- cong⊗r+⇑Q₁ refl = refl
-- -- -- cong⊗r+⇑Q₁ (~ eq) = ~ (cong⊗r+⇑Q₁ eq)
-- -- -- cong⊗r+⇑Q₁ (eq • eq₁) = (cong⊗r+⇑Q₁ eq) • (cong⊗r+⇑Q₁ eq₁)
-- -- -- cong⊗r+⇑Q₁ (Il eq) = Il (cong⊗r+⇑Q₁ eq)
-- -- -- cong⊗r+⇑Q₁ (⊗l eq) = ⊗l (cong⊗r+⇑Q₁ eq)
-- -- -- cong⊗r+⇑Q₁ (foc eq) = foc (cong⊗r+⇓Q₁ eq)

-- -- -- cong⊗r+⇓Q₂ : ∀ {b S Γ Δ₀ B₀ Q q Ξ}
-- -- --              (f : [ b , ∘ ] S ∣ Γ ⇓ Q) → 
-- -- --              {gs gs' : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → gs ≗s⇑ gs' →  
-- -- --        ---------------------------------------------------------------------
-- -- --            ⊗r+⇓Q Δ₀ q Ξ f gs ≗⇓ ⊗r+⇓Q Δ₀ q Ξ f gs'

-- -- -- cong⊗r+⇑Q₂ : ∀ {S Γ Δ₀ B₀ Q q Ξ}
-- -- --              (f : S ∣ Γ ⇑ Q) → 
-- -- --              {gs gs' : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → gs ≗s⇑ gs' →  
-- -- --        ---------------------------------------------------------------------
-- -- --            ⊗r+⇑Q Δ₀ q Ξ f gs ≗⇑ ⊗r+⇑Q Δ₀ q Ξ f gs'

-- -- -- cong⊗r+⇓Q₂ (focl q lf f eq) eqs = focl refl (cong⊗r+⇓Q₂ f eqs)
-- -- -- cong⊗r+⇓Q₂ (focr (just _) rf f eq) eqs = focr (++rf≗₂ rf eqs) refl
-- -- -- cong⊗r+⇓Q₂ (focr ─ rf f eq) eqs = focrn (++rf≗₂ rf eqs)
-- -- -- cong⊗r+⇓Q₂ {∙} {just P} (unfoc ok f) eqs = unfoc (cong⊗r+⇑Q₂ f eqs)

-- -- -- cong⊗r+⇑Q₂ (Il q f) eqs = Il (cong⊗r+⇑Q₂ f eqs)
-- -- -- cong⊗r+⇑Q₂ (⊗l q f) eqs = ⊗l (cong⊗r+⇑Q₂ f eqs)
-- -- -- cong⊗r+⇑Q₂ (foc s q f) eqs = foc (cong⊗r+⇓Q₂ f eqs)

-- -- -- cong⊗r+⇑Q : ∀ {S Γ Δ₀ B₀ Q q Ξ}
-- -- --              {f f' : S ∣ Γ ⇑ Q} → f ≗⇑ f' →
-- -- --              {gs gs' : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → gs ≗s⇑ gs' →  
-- -- --        ---------------------------------------------------------------------
-- -- --            ⊗r+⇑Q Δ₀ q Ξ f gs ≗⇑ ⊗r+⇑Q Δ₀ q Ξ f' gs'
-- -- -- cong⊗r+⇑Q {f' = f'} eq eqs = cong⊗r+⇑Q₁ eq • cong⊗r+⇑Q₂ f' eqs 

-- -- -- cong⊗r+⇑N₁ : ∀ {S Γ₀ Γ Γ₁ Δ₀ A B₀ n Ξ}
-- -- --            {f g : S ∣ Γ ⇑ A} → f ≗⇑ g → 
-- -- --            {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)}
-- -- --            {eq : Γ ≡ Γ₀ ++ Γ₁} →
-- -- --            ⊗r+⇑N Γ₁ Δ₀ n Ξ f gs eq ≗⇑ ⊗r+⇑N Γ₁ Δ₀ n Ξ g gs eq
-- -- -- cong⊗r+⇑N₁ refl {eq = refl} = refl
-- -- -- cong⊗r+⇑N₁ (~ eq) = ~ (cong⊗r+⇑N₁ eq)
-- -- -- cong⊗r+⇑N₁ (eq • eq₁) = cong⊗r+⇑N₁ eq • cong⊗r+⇑N₁ eq₁
-- -- -- cong⊗r+⇑N₁ (⊸r eq) {eq = refl} = cong⊗r+⇑N₁ eq
-- -- -- cong⊗r+⇑N₁ (Il eq) = Il (cong⊗r+⇑N₁ eq)
-- -- -- cong⊗r+⇑N₁ (⊗l eq) {eq = refl} = ⊗l (cong⊗r+⇑N₁ eq)
-- -- -- cong⊗r+⇑N₁ {Γ₁ = Γ₁} (foc eq) {eq = refl} = foc (focr refl (unfoc (cong⊸r⋆⇑ Γ₁ (foc eq))))

-- -- -- cong⊗r+⇑N₂ : ∀ {S Γ₀ Γ Γ₁ Δ₀ A B₀ n Ξ}
-- -- --            (f : S ∣ Γ ⇑ A) → 
-- -- --            {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → fs ≗s⇑ gs → 
-- -- --            {eq : Γ ≡ Γ₀ ++ Γ₁} →
-- -- --            ⊗r+⇑N Γ₁ Δ₀ n Ξ f fs eq ≗⇑ ⊗r+⇑N Γ₁ Δ₀ n Ξ f gs eq
-- -- -- cong⊗r+⇑N₂ (⊸r f) eqs {refl} = cong⊗r+⇑N₂ f eqs
-- -- -- cong⊗r+⇑N₂ (Il q f) eqs {eq} = Il (cong⊗r+⇑N₂ f eqs)
-- -- -- cong⊗r+⇑N₂ (⊗l q f) eqs {refl} = ⊗l (cong⊗r+⇑N₂ f eqs)
-- -- -- cong⊗r+⇑N₂ (foc s q f) eqs {refl} = foc (focr (⊗r+ refl eqs) refl)

-- -- -- cong⊗r+⇑N : ∀ {S Γ₀ Γ Γ₁ Δ₀ A B₀ n Ξ}
-- -- --            {f g : S ∣ Γ ⇑ A} → f ≗⇑ g → 
-- -- --            {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → fs ≗s⇑ gs → 
-- -- --            {eq : Γ ≡ Γ₀ ++ Γ₁} →
-- -- --            ⊗r+⇑N Γ₁ Δ₀ n Ξ f fs eq ≗⇑ ⊗r+⇑N Γ₁ Δ₀ n Ξ g gs eq
-- -- -- cong⊗r+⇑N {g = g} eq eqs = cong⊗r+⇑N₁ eq • cong⊗r+⇑N₂ g eqs

-- -- -- cong⊗r+⇑ : {S : Stp} {Γ : Cxt} {Δ₀ : Cxt} {B₀ A : Fma}
-- -- --            {Ξ : List (Cxt × Fma)}
-- -- --            {f f' : S ∣ Γ ⇑ A} → f ≗⇑ f' →
-- -- --            {gs gs' : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} → gs ≗s⇑ gs' → 
-- -- --     ---------------------------------------------------------------------
-- -- --           ⊗r+⇑ Δ₀ Ξ f gs ≗⇑ ⊗r+⇑ Δ₀ Ξ f' gs'
-- -- -- cong⊗r+⇑ {A = ` X} eq eqs = cong⊗r+⇑Q eq eqs
-- -- -- cong⊗r+⇑ {A = I} eq eqs = cong⊗r+⇑Q eq eqs
-- -- -- cong⊗r+⇑ {A = A ⊗ B} eq eqs = cong⊗r+⇑Q eq eqs
-- -- -- cong⊗r+⇑ {A = A ⊸ B} eq eqs = cong⊗r+⇑N eq eqs

-- -- -- cong⊗r⋆⇑ : {S : Stp} {Γ : Cxt} {A : Fma} {Ξ : List (Cxt × Fma)}
-- -- --            {f f' : S ∣ Γ ⇑ A} → f ≗⇑ f' →
-- -- --            {gs gs' : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ} → gs ≗s⇑ gs' → 
-- -- --     ---------------------------------------------------------------------
-- -- --           ⊗r⋆⇑ f gs ≗⇑ ⊗r⋆⇑ f' gs'
-- -- -- cong⊗r⋆⇑ eq [] = eq
-- -- -- cong⊗r⋆⇑ eq (eq' ∷ eqs) = cong⊗r+⇑ eq (eq' ∷ eqs)


-- -- -- ⊸r⋆⇑⊸l+⇑M : ∀ Γ {Γ₀ Δ A₀ M C m Ξ}
-- -- --              {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)} 
-- -- --             {f : just M ∣ Δ ++ Γ ⇑ C} →
-- -- --              ⊸l+⇑M Γ₀ m Ξ fs (⊸r⋆⇑ Γ f) ≡ ⊸r⋆⇑ Γ (⊸l+⇑M Γ₀ m Ξ fs f)
-- -- -- ⊸r⋆⇑⊸l+⇑M [] = refl
-- -- -- ⊸r⋆⇑⊸l+⇑M (B ∷ Γ) = cong ⊸r (⊸r⋆⇑⊸l+⇑M Γ)

-- -- -- early-lf⇓-at : ∀ Γ {Γ₀ Δ A₀ X Q n q Ξ}
-- -- --          (x : isAt X)
-- -- --          {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)} → 
-- -- --          (f : [ ∘ , ∘ ] just X ∣ Δ ++ Γ ⇓ Q) →
-- -- --          unfoc {∘}{∙} n (⊸r⋆⇑ {Γ = Γ₀ ++ concat (cxts Ξ) ++ Δ} Γ (foc tt q (⊸l+⇓M Γ₀ (at→negat x) Ξ fs f)))
-- -- --            ≗⇓ focl (at→posat x) (⊸l+ Γ₀ Ξ (at→posat x) fs blurl refl) (unfoc (inj₂ n) (⊸r⋆⇑ Γ (foc (at→negat x) q f))) refl

-- -- -- early-lf⇑-at : ∀ Γ {Γ₀ Δ A₀ X C n Ξ}
-- -- --          (x : isAt X)
-- -- --          {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)} → 
-- -- --          (f : just X ∣ Δ ++ Γ ⇑ C) →
-- -- --          unfoc {∘}{∙} n (⊸r⋆⇑ {Γ = Γ₀ ++ concat (cxts Ξ) ++ Δ} Γ (⊸l+⇑M Γ₀ (at→negat x) Ξ fs f))
-- -- --            ≗⇓ focl (at→posat x) (⊸l+ Γ₀ Ξ (at→posat x) fs blurl refl) (unfoc (inj₂ n) (⊸r⋆⇑ Γ f)) refl

-- -- -- early-lf⇑-at Γ x (⊸r f) =
-- -- --   unfoc-same (~ (refl⇑ (⊸r⋆⊸r⋆⇑ Γ {_ ∷ []})))
-- -- --   • early-lf⇑-at (Γ ∷ʳ _) x f
-- -- --   • focl refl (unfoc (refl⇑ (⊸r⋆⊸r⋆⇑ Γ {_ ∷ []})))
-- -- -- early-lf⇑-at Γ {X = ` X} x (foc s q f) = early-lf⇓-at Γ x f

-- -- -- early-lf⇓-at Γ {X = ` X} {q = q} x (focr (just (M , m)) rf (focl _ blurl f refl) eq) =
-- -- --   unfoc-same (cong⊸r⋆⇑ Γ (foc-same (~ swap'' eq)))
-- -- --   • early-lf-at Γ q {eq = refl}
-- -- --   • focl refl (unfoc (cong⊸r⋆⇑ Γ (foc-same (swap'' eq))))
-- -- -- early-lf⇓-at Γ {Γ₀} {X = ` X} {q = q} {Ξ = Ξ} x (focr (just (M , m)) rf (unfoc ok f) eq) =
-- -- --   unfoc-same (cong⊸r⋆⇑ Γ (foc-same (focr refl {eq' = cong (λ x → Γ₀ ++ concat (cxts Ξ) ++ x) eq} (early-lf⇑-at [] tt f) • (~ swap'' eq))))
-- -- --   • early-lf-at Γ q {eq = refl}
-- -- --   • focl refl (unfoc (cong⊸r⋆⇑ Γ (foc-same (swap'' eq {eq} • focr refl blurl-at))))
-- -- -- early-lf⇓-at Γ {X = ` X} {q = q} x (focl _ blurl f refl) = early-lf-at Γ q

-- -- -- cong⊸l+⇓M₁ : ∀ {b Γ₀ Δ A₀ M C m Ξ}
-- -- --          {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)} → fs ≗s⇑ gs → 
-- -- --          (f : [ ∘ , b ] just M ∣ Δ ⇓ C) →
-- -- --          ⊸l+⇓M Γ₀ m Ξ fs f ≗⇓ ⊸l+⇓M Γ₀ m Ξ gs f

-- -- -- cong⊸l+⇑M₁ : ∀ {Γ₀ Δ A₀ M C m Ξ}
-- -- --          {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)} → fs ≗s⇑ gs → 
-- -- --          (f : just M ∣ Δ ⇑ C) →
-- -- --          ⊸l+⇑M Γ₀ m Ξ fs f ≗⇑ ⊸l+⇑M Γ₀ m Ξ gs f

-- -- -- cong⊸l+⇑M₁ eqs (⊸r f) = ⊸r (cong⊸l+⇑M₁ eqs f)
-- -- -- cong⊸l+⇑M₁ eqs (foc s q f) = foc (cong⊸l+⇓M₁ eqs f)

-- -- -- cong⊸l+⇓M₁ eqs (focl q lf f refl) = focl (++lf≗₂ lf eqs) refl
-- -- -- cong⊸l+⇓M₁ eqs (focr (just _) rf f refl) = focr refl (cong⊸l+⇓M₁ eqs f)
-- -- -- cong⊸l+⇓M₁ {∙} eqs (unfoc ok f) = unfoc (cong⊸l+⇑M₁ eqs f)

-- -- -- cong⊸l+⇓M₂ : ∀ {b Γ₀ Δ A₀ M C m Ξ}
-- -- --          {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)} 
-- -- --          {f g : [ ∘ , b ] just M ∣ Δ ⇓ C} → f ≗⇓ g → 
-- -- --          ⊸l+⇓M Γ₀ m Ξ fs f ≗⇓ ⊸l+⇓M Γ₀ m Ξ fs g

-- -- -- cong⊸l+⇑M₂ : ∀ {Γ₀ Δ A₀ M C m Ξ}
-- -- --          {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)} 
-- -- --          {f g : just M ∣ Δ ⇑ C} → f ≗⇑ g → 
-- -- --          ⊸l+⇑M Γ₀ m Ξ fs f ≗⇑ ⊸l+⇑M Γ₀ m Ξ fs g

-- -- -- cong⊸l+⇑M₂ refl = refl
-- -- -- cong⊸l+⇑M₂ (~ eq) = ~ (cong⊸l+⇑M₂ eq)
-- -- -- cong⊸l+⇑M₂ (eq • eq₁) = cong⊸l+⇑M₂ eq • cong⊸l+⇑M₂ eq₁
-- -- -- cong⊸l+⇑M₂ (⊸r eq) = ⊸r (cong⊸l+⇑M₂ eq)
-- -- -- cong⊸l+⇑M₂ (foc eq) = foc (cong⊸l+⇓M₂ eq)

-- -- -- cong⊸l+⇓M₂ refl = refl
-- -- -- cong⊸l+⇓M₂ (~ eq) = ~ cong⊸l+⇓M₂ eq
-- -- -- cong⊸l+⇓M₂ (eq • eq₁) = cong⊸l+⇓M₂ eq • cong⊸l+⇓M₂ eq₁
-- -- -- cong⊸l+⇓M₂ (focl eql {eq = refl}{refl} eq) = focl (++lf≗₁ eql) eq
-- -- -- cong⊸l+⇓M₂ (focr eqr {eq = refl}{refl} eq) = focr eqr (cong⊸l+⇓M₂ eq)
-- -- -- cong⊸l+⇓M₂ {∙} (unfoc eq) = unfoc (cong⊸l+⇑M₂ eq)
-- -- -- cong⊸l+⇓M₂ swap = swap
-- -- -- cong⊸l+⇓M₂ (early-lf Δ r {eq = refl}{refl}) = unfoc-same (refl⇑ (⊸r⋆⇑⊸l+⇑M Δ)) • early-lf Δ r
-- -- -- cong⊸l+⇓M₂ (early-lf-at Δ r {eq = refl}{refl}) = unfoc (refl⇑ (⊸r⋆⇑⊸l+⇑M Δ)) • early-lf-at Δ r
-- -- -- cong⊸l+⇓M₂ blurl-at = ~ early-lf⇑-at [] _ _

-- -- -- cong⊸l+⇑M : ∀ {Γ₀ Δ A₀ M C m Ξ}
-- -- --          {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)} → fs ≗s⇑ gs → 
-- -- --          {f g : just M ∣ Δ ⇑ C} → f ≗⇑ g → 
-- -- --          ⊸l+⇑M Γ₀ m Ξ fs f ≗⇑ ⊸l+⇑M Γ₀ m Ξ gs g
-- -- -- cong⊸l+⇑M eqs {f} eq = cong⊸l+⇑M₁ eqs f • cong⊸l+⇑M₂ eq

-- -- -- cong⊸l+⇑P₁ : ∀ {S Γ₀ Δ₀ Δ₁ Δ A₀ P C p Ξ}
-- -- --              {fs fs' : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)} → fs ≗s⇑ fs' → 
-- -- --              (f : S ∣ Δ ⇑ C)
-- -- --              {eq : Δ ≡ Δ₀ ++ Δ₁}
-- -- --              {ℓ : L S Δ₀ P} →
-- -- --              ⊸l+⇑P Γ₀ Δ₀ Δ₁ p Ξ fs f eq ℓ ≗⇑ ⊸l+⇑P Γ₀ Δ₀ Δ₁ p Ξ fs' f eq ℓ
-- -- -- cong⊸l+⇑P₁ eqs (⊸r f) {refl} = ⊸r (cong⊸l+⇑P₁ eqs f)
-- -- -- cong⊸l+⇑P₁ eqs (Il q f) {refl} = cong⊸l+⇑P₁ eqs f
-- -- -- cong⊸l+⇑P₁ eqs (⊗l q f) {refl} = cong⊸l+⇑P₁ eqs f
-- -- -- cong⊸l+⇑P₁ eqs (foc s q f) {refl} = foc (focl (⊸l+ eqs refl) refl)

-- -- -- cong⊸l+⇑P₂ : ∀ {S Γ₀ Δ₀ Δ₁ Δ A₀ P C p Ξ}
-- -- --              {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)}  
-- -- --              {f g : S ∣ Δ ⇑ C} → f ≗⇑ g → 
-- -- --              {eq : Δ ≡ Δ₀ ++ Δ₁}
-- -- --              {ℓ : L S Δ₀ P} →
-- -- --              ⊸l+⇑P Γ₀ Δ₀ Δ₁ p Ξ fs f eq ℓ ≗⇑ ⊸l+⇑P Γ₀ Δ₀ Δ₁ p Ξ fs g eq ℓ
-- -- -- cong⊸l+⇑P₂ refl = refl
-- -- -- cong⊸l+⇑P₂ (~ eq) = ~ (cong⊸l+⇑P₂ eq)
-- -- -- cong⊸l+⇑P₂ (eq • eq₁) = cong⊸l+⇑P₂ eq • cong⊸l+⇑P₂ eq₁
-- -- -- cong⊸l+⇑P₂ (⊸r eq) {refl} = ⊸r (cong⊸l+⇑P₂ eq)
-- -- -- cong⊸l+⇑P₂ (Il eq) = cong⊸l+⇑P₂ eq
-- -- -- cong⊸l+⇑P₂ (⊗l eq) {refl} = cong⊸l+⇑P₂ eq
-- -- -- cong⊸l+⇑P₂ (foc eq) {refl} {ℓ} = foc (focl refl (unfoc (congrunLQ ℓ (foc eq))))

-- -- -- cong⊸l+⇑P : ∀ {S Γ₀ Δ₀ Δ₁ Δ A₀ P C p Ξ}
-- -- --              {fs gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)} → fs ≗s⇑ gs → 
-- -- --              {f g : S ∣ Δ ⇑ C} → f ≗⇑ g → 
-- -- --              {eq : Δ ≡ Δ₀ ++ Δ₁}
-- -- --              {ℓ : L S Δ₀ P} →
-- -- --              ⊸l+⇑P Γ₀ Δ₀ Δ₁ p Ξ fs f eq ℓ ≗⇑ ⊸l+⇑P Γ₀ Δ₀ Δ₁ p Ξ gs g eq ℓ
-- -- -- cong⊸l+⇑P eqs {f} eq = cong⊸l+⇑P₁ eqs f • cong⊸l+⇑P₂ eq

-- -- -- cong⊸l+⇑ : {Γ₀ : Cxt} {Δ : Cxt} {A₀ B C : Fma}
-- -- --          {Ξ : List (Cxt × Fma)}
-- -- --          {fs fs' : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)} → fs ≗s⇑ fs' →
-- -- --          {g g' : just B ∣ Δ ⇑ C} → g ≗⇑ g' → 
-- -- --     ---------------------------------------------------------------------
-- -- --           ⊸l+⇑ Γ₀ Ξ fs g ≗⇑ ⊸l+⇑ Γ₀ Ξ fs' g'
-- -- -- cong⊸l+⇑ {B = ` X} eqs eq = cong⊸l+⇑M eqs eq
-- -- -- cong⊸l+⇑ {B = I} eqs eq = cong⊸l+⇑P eqs eq
-- -- -- cong⊸l+⇑ {B = A ⊗ B} eqs eq = cong⊸l+⇑P eqs eq
-- -- -- cong⊸l+⇑ {B = A ⊸ B} eqs eq = cong⊸l+⇑M eqs eq

-- -- -- cong⊸l⋆⇑ : {Δ : Cxt} {B C : Fma} {Ξ : List (Cxt × Fma)}
-- -- --          {fs fs' : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) Ξ} → fs ≗s⇑ fs' →
-- -- --          {g g' : just B ∣ Δ ⇑ C} → g ≗⇑ g' → 
-- -- --     ---------------------------------------------------------------------
-- -- --           ⊸l⋆⇑ fs g ≗⇑ ⊸l⋆⇑ fs' g'
-- -- -- cong⊸l⋆⇑ [] eq = eq
-- -- -- cong⊸l⋆⇑ (eq₁ ∷ eqs) eq = cong⊸l+⇑ (eq₁ ∷ eqs) eq

-- -- -- ⊗r+⇓Qpass⇓ : ∀ {Γ Δ₀ A B₀ Q q Ξ}
-- -- --              (f : [ ∘ , ∘ ] just A ∣ Γ ⇓ Q)
-- -- --              {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} →
-- -- --              ⊗r+⇓Q Δ₀ q Ξ (pass⇓ f) gs ≗⇓ pass⇓ (⊗r+⇓Q Δ₀ q Ξ f gs)

-- -- -- ⊗r+⇑Qpass⇑ : ∀ {Γ Δ₀ A B₀ Q q Ξ}
-- -- --              (f : just A ∣ Γ ⇑ Q)
-- -- --              {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} →
-- -- --              ⊗r+⇑Q Δ₀ q Ξ (pass⇑ f) gs ≗⇑ pass⇑ (⊗r+⇑Q Δ₀ q Ξ f gs)

-- -- -- ⊗r+⇓Qpass⇓ (focl q lf f refl) = refl
-- -- -- ⊗r+⇓Qpass⇓ (focr (just x) rf f refl) = refl

-- -- -- ⊗r+⇑Qpass⇑ (Il q f) = refl
-- -- -- ⊗r+⇑Qpass⇑ (⊗l q f) = refl
-- -- -- ⊗r+⇑Qpass⇑ (foc s q f) = foc (⊗r+⇓Qpass⇓ f)


-- -- -- ⊗r+⇑Npass⇑ : ∀ {Γ₀ Γ Γ₁ Δ₀ A A' B₀ n Ξ}
-- -- --            (f : just A' ∣ Γ ⇑ A)
-- -- --            {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)}
-- -- --            {eq : Γ ≡ Γ₀ ++ Γ₁} →
-- -- --            ⊗r+⇑N Γ₁ Δ₀ n Ξ (pass⇑ f) gs (cong (A' ∷_) eq) ≗⇑ pass⇑ (⊗r+⇑N Γ₁ Δ₀ n Ξ f gs eq)
-- -- -- ⊗r+⇑Npass⇑ (⊸r f) {eq = refl} = ⊗r+⇑Npass⇑ f
-- -- -- ⊗r+⇑Npass⇑ {Γ₁ = Γ₁} {Ξ = Ξ} (Il q f) {eq = refl} =
-- -- --   foc (focr refl (early-lf _ q)
-- -- --        • ~ swap
-- -- --        • focl refl (focr refl (unfoc (refl⇑ (trans (cong (⊸r⋆⇑ Γ₁) (sym (Il⇑eq f))) (⊸r⋆Il⇑ Γ₁))))
-- -- --                               • ~ early-rf⇑N f (Il-1 done)
-- -- --                               • unfoc (refl⇑ (Il⇑eq _))))
-- -- -- ⊗r+⇑Npass⇑ {Γ₁ = Γ₁} {Ξ = Ξ} (⊗l q f) {eq = refl} =
-- -- --   foc (focr refl (early-lf _ q)
-- -- --        • ~ swap
-- -- --        • focl refl (focr refl (unfoc (refl⇑ (trans (cong (⊸r⋆⇑ Γ₁) (sym (⊗l⇑eq f))) (⊸r⋆⊗l⇑ Γ₁))))
-- -- --                                • ~ early-rf⇑N f (⊗l-1 done)
-- -- --                                • unfoc (refl⇑ (⊗l⇑eq _))))
-- -- -- ⊗r+⇑Npass⇑ {Γ₁ = Γ₁} (foc s q f) {eq = refl} =
-- -- --   foc (focr refl (unfoc (refl⇑ (sym (pass⊸r⋆⇑ Γ₁)))))

-- -- -- ⊗r+pass⇑ : ∀ {Γ Δ₀ A B₀ C Ξ}
-- -- --              {f : just A ∣ Γ ⇑ C}
-- -- --              {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ)} →
-- -- --              ⊗r+⇑ Δ₀ Ξ (pass⇑ f) gs ≗⇑ pass⇑ (⊗r+⇑ Δ₀ Ξ f gs)
-- -- -- ⊗r+pass⇑ {C = ` X} = ⊗r+⇑Qpass⇑ _
-- -- -- ⊗r+pass⇑ {C = I} = ⊗r+⇑Qpass⇑ _
-- -- -- ⊗r+pass⇑ {C = C ⊗ C₁} = ⊗r+⇑Qpass⇑ _
-- -- -- ⊗r+pass⇑ {C = C ⊸ C₁} {f = f} = ⊗r+⇑Npass⇑ f

-- -- -- ⊗rpass⇑ : ∀ {Γ Δ A' A B}
-- -- --           {f : just A' ∣ Γ ⇑ A}
-- -- --           {g : ─ ∣ Δ ⇑ B} → 
-- -- --           ⊗r⇑ (pass⇑ f) g ≗⇑ pass⇑ (⊗r⇑ f g)
-- -- -- ⊗rpass⇑ = ⊗r+pass⇑ {gs = _ ∷ []}

-- -- -- ⊗r+⇓Q⊸l+⇓M : ∀ {Γ₀ Δ₀ Λ A₀ B₀ A B Ξ Ξ' q m}
-- -- --              {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)}
-- -- --              (h : [ ∘ , ∘ ] just B ∣ Λ ⇓ A)
-- -- --              {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ')} →
-- -- --              ⊗r+⇓Q Δ₀ q Ξ' (⊸l+⇓M Γ₀ m Ξ fs h) gs ≗⇓ ⊸l+⇓M Γ₀ m Ξ fs (⊗r+⇓Q Δ₀ q Ξ' h gs)
 
-- -- -- ⊗r+⇑Q⊸l+⇑M : ∀ {Γ₀ Δ₀ Λ A₀ B₀ A B Ξ Ξ' q m}
-- -- --              {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)}
-- -- --              (h : just B ∣ Λ ⇑ A)
-- -- --              {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ')} →
-- -- --              ⊗r+⇑Q Δ₀ q Ξ' (⊸l+⇑M Γ₀ m Ξ fs h) gs ≗⇑ ⊸l+⇑M Γ₀ m Ξ fs (⊗r+⇑Q Δ₀ q Ξ' h gs)

-- -- -- ⊗r+⇑Q⊸l+⇑M (foc s q f) = foc (⊗r+⇓Q⊸l+⇓M f)

-- -- -- ⊗r+⇓Q⊸l+⇓M (focl q lf h eq) = focl refl refl
-- -- -- ⊗r+⇓Q⊸l+⇓M (focr (just _) rf f eq) = focr refl refl

-- -- -- ⊗r+⇑Q⊸l+⇑P : ∀ {S Γ₀ Γ₁ Δ₀ Δ₁ Δ A₀ A₁ P Q p q Ξ Ξ'}
-- -- --              {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)} → 
-- -- --              (f : S ∣ Δ ⇑ Q)
-- -- --              {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₁ , A₁) ∷ Ξ')} → 
-- -- --              {eq : Δ ≡ Δ₀ ++ Δ₁}
-- -- --              {ℓ : L S Δ₀ P} →
-- -- --              ⊗r+⇑Q Γ₁ q Ξ' (⊸l+⇑P Γ₀ Δ₀ Δ₁ p Ξ fs f eq ℓ) gs
-- -- --                ≗⇑ ⊸l+⇑P Γ₀ Δ₀ (Δ₁ ++ Γ₁ ++ concat (cxts Ξ')) p Ξ fs (⊗r+⇑Q Γ₁ q Ξ' f gs) (cong (λ x → x ++ Γ₁ ++ concat (cxts Ξ')) eq) ℓ
-- -- -- ⊗r+⇑Q⊸l+⇑P (Il q f) = ⊗r+⇑Q⊸l+⇑P f
-- -- -- ⊗r+⇑Q⊸l+⇑P (⊗l q f) {eq = refl} = ⊗r+⇑Q⊸l+⇑P f
-- -- -- ⊗r+⇑Q⊸l+⇑P (foc s q f) {eq = refl} {ℓ} = foc (focl refl (unfoc (refl⇑ (runLQ⊗r+⇑Q ℓ))))

-- -- -- ⊗r+⇑N⊸l+⇑M : ∀ {Γ₀ Γ Γ₁ Δ₀ Δ₁ A A₀ B₀ M n m Ξ Ξ'}
-- -- --              {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₁ , A₀) ∷ Ξ)} → 
-- -- --              (f : just M ∣ Γ ⇑ A)
-- -- --              {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ')}
-- -- --              {eq : Γ ≡ Γ₀ ++ Γ₁} →
-- -- --              ⊗r+⇑N {Γ₀ = Δ₁ ++ concat (cxts Ξ) ++ Γ₀} Γ₁ Δ₀ n Ξ' (⊸l+⇑M Δ₁ m Ξ fs f) gs (cong (λ x → Δ₁ ++ concat (cxts Ξ) ++ x) eq)
-- -- --                ≗⇑ ⊸l+⇑M Δ₁ m Ξ fs (⊗r+⇑N Γ₁ Δ₀ n Ξ' f gs eq)
-- -- -- ⊗r+⇑N⊸l+⇑M (⊸r f) {eq = refl} = ⊗r+⇑N⊸l+⇑M f
-- -- -- ⊗r+⇑N⊸l+⇑M {Γ₁ = Γ₁} (foc s q f) {eq = refl} = foc (focr refl (unfoc (~ (refl⇑ (⊸r⋆⇑⊸l+⇑M Γ₁)))))

-- -- -- ⊗r+⇑N⊸l+⇑P : ∀ {S Γ₀ Γ Γ₁ Γ₀' Γ₁' Δ₀ Δ₁ A A₀ B₀ P n p Ξ Ξ'}
-- -- --              {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₁ , A₀) ∷ Ξ)} → 
-- -- --              (f : S ∣ Γ ⇑ A)
-- -- --              {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ')}
-- -- --              {eq : Γ ≡ Γ₀' ++ Γ₁'}
-- -- --              {eq' : Γ₁' ≡ Γ₀ ++ Γ₁}
-- -- --              {ℓ : L S Γ₀' P} →
-- -- --              ⊗r+⇑N {Γ₀ = Δ₁ ++ concat (cxts Ξ) ++ Γ₀} Γ₁ Δ₀ n Ξ' (⊸l+⇑P Δ₁ Γ₀' Γ₁' p Ξ fs f eq ℓ) gs (cong (λ x → Δ₁ ++ concat (cxts Ξ) ++ x) eq')
-- -- --                ≗⇑ ⊸l+⇑P Δ₁ Γ₀' (Γ₀ ++ Δ₀ ++ concat (cxts Ξ')) p Ξ fs (⊗r+⇑N {Γ₀ = Γ₀' ++ Γ₀} Γ₁ Δ₀ n Ξ' f gs (trans eq (cong (λ x → Γ₀' ++ x) eq'))) refl ℓ
-- -- -- ⊗r+⇑N⊸l+⇑P {Γ₀ = Γ₀} (⊸r f) {eq = refl} {refl} = ⊗r+⇑N⊸l+⇑P {Γ₀ = Γ₀} f
-- -- -- ⊗r+⇑N⊸l+⇑P (Il q f) {eq = refl} {refl} = ⊗r+⇑N⊸l+⇑P f
-- -- -- ⊗r+⇑N⊸l+⇑P (⊗l q f) {eq = refl} {refl} = ⊗r+⇑N⊸l+⇑P f
-- -- -- ⊗r+⇑N⊸l+⇑P {Γ₀ = Γ₀} {Γ₁ = Γ₁} {Γ₀'}{Γ₁'}{Δ₀} {n = n} {Ξ' = Ξ'} (foc s q f) {eq = refl} {refl} {ℓ} =
-- -- --   foc (focr refl (early-lf _ q)
-- -- --       • ~ swap
-- -- --       • focl refl (~ (unfoc-same (refl⇑ (sym (runLeq ℓ)))
-- -- --                       • early-rf s {r = isPosAt⊗⋆ tt (fmas Ξ')} {f = ⊸r⋆⇑ Γ₁ (foc s q f)} ℓ {eq = refl}
-- -- --                       • focr refl (unfoc (refl⇑ (sym (⊸r⋆runL Γ₁ ℓ)) • cong⊸r⋆⇑ Γ₁ (refl⇑ (runLeq ℓ)))))))

-- -- -- ⊗r+⊸l+⇑ : ∀ {Γ₀ Δ₀ Λ A₀ B₀ A B Ξ Ξ'}
-- -- --             {fs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Γ₀ , A₀) ∷ Ξ)}
-- -- --             {h : just B ∣ Λ ⇑ A}
-- -- --             {gs : All (λ ΔB → ─ ∣ proj₁ ΔB ⇑ proj₂ ΔB) ((Δ₀ , B₀) ∷ Ξ')} →
-- -- --             ⊗r+⇑ Δ₀ Ξ' (⊸l+⇑ Γ₀ Ξ fs h) gs ≗⇑ ⊸l+⇑ Γ₀ Ξ fs (⊗r+⇑ Δ₀ Ξ' h gs)
-- -- -- ⊗r+⊸l+⇑ {A = ` X} {` Y} = ⊗r+⇑Q⊸l+⇑M _
-- -- -- ⊗r+⊸l+⇑ {A = ` X} {I} {h = h} = ⊗r+⇑Q⊸l+⇑P h
-- -- -- ⊗r+⊸l+⇑ {A = ` X} {A' ⊗ B'} {h = h} = ⊗r+⇑Q⊸l+⇑P h
-- -- -- ⊗r+⊸l+⇑ {A = ` X} {A' ⊸ B'} = ⊗r+⇑Q⊸l+⇑M _
-- -- -- ⊗r+⊸l+⇑ {A = I} {` Y} = ⊗r+⇑Q⊸l+⇑M _
-- -- -- ⊗r+⊸l+⇑ {A = I} {I} {h = h} = ⊗r+⇑Q⊸l+⇑P h
-- -- -- ⊗r+⊸l+⇑ {A = I} {A' ⊗ B'} {h = h} = ⊗r+⇑Q⊸l+⇑P h
-- -- -- ⊗r+⊸l+⇑ {A = I} {A' ⊸ B'} = ⊗r+⇑Q⊸l+⇑M _
-- -- -- ⊗r+⊸l+⇑ {A = A ⊗ B} {` X} = ⊗r+⇑Q⊸l+⇑M _
-- -- -- ⊗r+⊸l+⇑ {A = A ⊗ B} {I} {h = h} = ⊗r+⇑Q⊸l+⇑P h
-- -- -- ⊗r+⊸l+⇑ {A = A ⊗ B} {A' ⊗ B'} {h = h} = ⊗r+⇑Q⊸l+⇑P h
-- -- -- ⊗r+⊸l+⇑ {A = A ⊗ B} {A' ⊸ B'} = ⊗r+⇑Q⊸l+⇑M _
-- -- -- ⊗r+⊸l+⇑ {A = A ⊸ B} {` Y} {h = h} = ⊗r+⇑N⊸l+⇑M h 
-- -- -- ⊗r+⊸l+⇑ {A = A ⊸ B} {I} {h = h} = ⊗r+⇑N⊸l+⇑P h
-- -- -- ⊗r+⊸l+⇑ {A = A ⊸ B} {A' ⊗ B'} {h = h} = ⊗r+⇑N⊸l+⇑P h
-- -- -- ⊗r+⊸l+⇑ {A = A ⊸ B} {A' ⊸ B'} {h = h} = ⊗r+⇑N⊸l+⇑M h

-- -- -- ⊗r⊸l⇑ : ∀ {Γ Δ Λ A A' B B'}
-- -- --           {f : ─ ∣ Γ ⇑ A'}
-- -- --           {h : just B' ∣ Λ ⇑ A}
-- -- --           {g : ─ ∣ Δ ⇑ B} → 
-- -- --           ⊗r⇑ (⊸l⇑ f h) g ≗⇑ ⊸l⇑ f (⊗r⇑ h g)
-- -- -- ⊗r⊸l⇑ = ⊗r+⊸l+⇑ {fs = _ ∷ []} {gs = _ ∷ []}


-- -- -- focus≗ : ∀ {S Γ A} {f g : S ∣ Γ ⊢ A}
-- -- --   → f ≗ g → focus f ≗⇑ focus g
-- -- -- focus≗ refl = refl
-- -- -- focus≗ (~ eq) = ~ (focus≗ eq)
-- -- -- focus≗ (eq • eq₁) = (focus≗ eq) • (focus≗ eq₁)
-- -- -- focus≗ (pass eq) = congpass⇑ (focus≗ eq)
-- -- -- focus≗ (Il eq) = congIl⇑ (focus≗ eq) 
-- -- -- focus≗ (⊗l eq) = cong⊗l⇑ (focus≗ eq)  
-- -- -- focus≗ (⊗r eq eq₁) = cong⊗r+⇑ (focus≗ eq) (focus≗ eq₁ ∷ []) 
-- -- -- focus≗ (⊸r eq) = ⊸r (focus≗ eq)
-- -- -- focus≗ (⊸l eq eq₁) = cong⊸l+⇑ (focus≗ eq ∷ []) (focus≗ eq₁) 
-- -- -- focus≗ (⊗rIl {Δ = Δ}) = refl⇑ (⊗r+Il⇑ Δ [] _ _)
-- -- -- focus≗ (⊗r⊗l {Δ = Δ}) = refl⇑ (⊗r+⊗l⇑ Δ [] _ _)
-- -- -- focus≗ ⊸rpass = refl
-- -- -- focus≗ ⊸rIl = refl
-- -- -- focus≗ ⊸r⊗l = refl
-- -- -- focus≗ ⊸r⊸l = refl⇑ (⊸r⊸l⇑ _ _)
-- -- -- focus≗ ⊗rpass = ⊗rpass⇑
-- -- -- focus≗ ⊗r⊸l = ⊗r⊸l⇑


-- -- -- -- focus∘emb⇑ : ∀ {S Γ A} (f : S ∣ Γ ⇑ A) → focus (emb⇑ f) ≗⇑ f
-- -- -- -- focus∘emb⇓ : ∀ {S Γ Q} (s : isIrr S) (q : isPosAt Q)
-- -- -- --   → (f : [ ∘ , ∘ ] S ∣ Γ ⇓ Q) → focus (emb⇓ f) ≗⇑ foc s q f

-- -- -- -- focus∘emb⇑ (⊸r f) = ⊸r (focus∘emb⇑ f)
-- -- -- -- focus∘emb⇑ (Il q f) = refl⇑ (Il⇑eq {q = q} _) • Il (focus∘emb⇑ f)
-- -- -- -- focus∘emb⇑ (⊗l q f) = refl⇑ (⊗l⇑eq {q = q} _) • ⊗l (focus∘emb⇑ f)
-- -- -- -- focus∘emb⇑ (foc s q f) = focus∘emb⇓ s q f 

-- -- -- -- focus∘emb⇓ s q (focl q₁ (pass (⊸l+ Γ₀ Ξ q₂ fs blurl refl)) f refl) = {!fs!}
-- -- -- -- focus∘emb⇓ s q (focl q₁ (pass blurl) (focr s₁ (⊗r+ Δ₀ Ξ m (⊗r+ Δ₁ Ξ₁ m₁ rf gs₁ eq₂) gs eq₁) f eq) refl) = ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ _ (fmas Ξ₁)) m)
-- -- -- -- focus∘emb⇓ s q (focl q₁ (pass blurl) (focr .(just (` _ , _)) (⊗r+ Δ₀ Ξ m blurr gs refl) ax refl) refl) = {!swapped!}
-- -- -- -- focus∘emb⇓ s q (focl q₁ (pass blurl) (focr .(just (_ , _)) (⊗r+ Δ₀ Ξ m blurr gs refl) (unfoc ok f) refl) refl) = {!swapped!}
-- -- -- -- focus∘emb⇓ s q (focl q₁ (pass blurl) (focr .(just (` _ , _)) blurr ax refl) refl) =
-- -- -- --   foc (focl refl (~ {!!}))
-- -- -- -- focus∘emb⇓ s q (focl q₁ (pass blurl) (focr .(just (_ , _)) blurr (unfoc ok f) refl) refl) = {!!}
-- -- -- -- focus∘emb⇓ s q (focl q₁ (pass blurl) (unfoc ok f) refl) = {!!}
-- -- -- -- focus∘emb⇓ s q (focl q₁ (⊸l+ Γ₀ Ξ q₂ fs blurl refl) f refl) = {!!}
-- -- -- -- focus∘emb⇓ s q (focl q₁ blurl f refl) = {!!}
-- -- -- -- focus∘emb⇓ s q (focr (just _) (⊗r+ Δ₀ Ξ m (⊗r+ Δ₁ Ξ₁ m₁ rf gs₁ eq₂) gs eq₁) f eq) =
-- -- -- --   ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ tt (fmas Ξ₁)) m)
-- -- -- -- focus∘emb⇓ s q (focr (just _) (⊗r+ Δ₀ Ξ m blurr gs refl) f refl) = {!!}
-- -- -- -- focus∘emb⇓ s q (focr (just _) blurr (focl q₁ lf f eq) refl) = {!!}
-- -- -- -- focus∘emb⇓ s q (focr (just _) blurr (unfoc ok f) refl) = {!imp!}
-- -- -- -- focus∘emb⇓ s q (focr ─ Ir (refl , refl) refl) = refl
-- -- -- -- focus∘emb⇓ s q (focr ─ (⊗r+ Δ₀ Ξ m Ir gs refl) (refl , refl) refl) = {!!}
-- -- -- -- focus∘emb⇓ s q (focr ─ (⊗r+ Δ₀ Ξ m (⊗r+ Δ₁ Ξ₁ m₁ rf gs₁ eq₂) gs eq₁) f eq) =
-- -- -- --   ⊥-elim (is⊗×isn't⊗→⊥ (is⊗⊗⋆ tt (fmas Ξ₁)) m)
-- -- -- -}
