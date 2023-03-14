{-# OPTIONS --rewriting #-}

module Utilities where

open import Data.Empty
open import Data.Maybe hiding (map)
open import Data.Sum hiding (map)
open import Data.List
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality

{-# BUILTIN REWRITE _≡_ #-}

-- uniqueness of identity proofs

uip : {A : Set} → {a a' : A} → {p p' : a ≡ a'} → p ≡ p' 
uip {_} {.a} {a} {refl} {refl} = refl

-- Some lemmata about lists for reasoning about contexts

++ru : {X : Set} → (xs : List X) → xs ++ [] ≡ xs
++ru [] = refl
++ru (x ∷ xs) = cong (_∷_ x) (++ru xs) 

++ass : {X : Set} → (xs : List X) → {ys zs : List X} → 
           (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++ass [] = refl
++ass (x ∷ xs) = cong (_∷_ x) (++ass xs)

{-# REWRITE ++ass #-}
{-# REWRITE ++ru #-}

-- We used Agda rewriting feature to turn the propositional equalities
-- ++ass and ++ru into judgemental equalities. This is not necessary,
-- but it makes things some things easier.

map++ : {A B : Set} (f : A → B) (xs ys : List A)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map++ f [] ys = refl
map++ f (x ∷ xs) ys = cong (f x ∷_) (map++ f xs ys)

map-id : {A : Set} (xs : List A)
  → map (λ x → x) xs ≡ xs
map-id [] = refl
map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

map-comp : {A B C : Set} (g : B → C) (f : A → B) (xs : List A)
  → map g (map f xs) ≡ map (λ x → g (f x)) xs
map-comp g f [] = refl
map-comp g f (x ∷ xs) = cong (g (f x) ∷_) (map-comp g f xs)

{-# REWRITE map++ #-}
{-# REWRITE map-id #-}
{-# REWRITE map-comp #-}

-- We turned map++, map-id and map-comp into judgemental equalities as
-- well.

-- Some properties of lists.
inj∷ : {X : Set} → {x y : X} → {xs ys : List X} → 
           x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
inj∷ refl = refl , refl

[]disj∷ : {X : Set} → (xs : List X) → {ys : List X} → {x : X} →  
             [] ≡ xs ++ x ∷ ys → ⊥
[]disj∷ [] ()
[]disj∷ (x ∷ xs) ()

cases∷ : {X : Set} → (xs : List X) → {ys ys' : List X} → {x x' : X} → 
   x' ∷ ys' ≡ xs ++ x ∷ ys → 
        (x ≡ x' × xs ≡ [] × ys ≡ ys')  
        ⊎ Σ (List X) 
               (λ xs₀  → ys' ≡ xs₀ ++ x ∷ ys × xs ≡ x' ∷ xs₀) 
cases∷ [] refl = inj₁ (refl , refl , refl)
cases∷ (x₀ ∷ xs) {ys} {.(xs ++ x ∷ ys)} {x} {.x₀} refl = inj₂ (xs , refl , refl)

cases++ : {X : Set} → (xs xs' ys ys' : List X) → {x : X} → 
   xs' ++ ys' ≡ xs ++ x ∷ ys → 
       Σ (List X) (λ xs₀ → xs' ≡ xs ++ x ∷ xs₀ × ys ≡ xs₀ ++ ys')  
     ⊎ Σ (List X) (λ xs₀ → ys' ≡ xs₀ ++ x ∷ ys × xs ≡ xs' ++ xs₀) 
cases++ xs [] _ _ refl = inj₂ (xs , refl , refl)
cases++ [] (x' ∷ xs') _ _ refl = inj₁ (xs' , refl , refl)
cases++ (x₀ ∷ xs) (x' ∷ xs') ys ys' {x} p with inj∷ p
cases++ (.x' ∷ xs) (x' ∷ xs') ys ys' p | refl , q with cases++ xs xs' ys ys' q 
cases++ (.x' ∷ xs) (x' ∷ xs') ys ys' p | refl , q | inj₁ (xs₀ , r , r') = inj₁ (xs₀ , cong₂ _∷_ refl r , r')
cases++ (.x' ∷ xs) (x' ∷ xs') ys ys' p | refl , q | inj₂ (xs₀ , r , r') = inj₂ (xs₀ , r , cong₂ _∷_ refl r')

cases++2 : {X : Set} → (xs xs' ys ys' : List X) → {x y z : X} → 
   xs' ++ y ∷ z ∷ ys' ≡ xs ++ x ∷ ys → 
       Σ (List X) (λ xs₀ → xs' ≡ xs ++ x ∷ xs₀ × ys ≡ xs₀ ++ y ∷ z ∷ ys')
     ⊎ Σ (List X) (λ xs₀ → ys' ≡ xs₀ ++ x ∷ ys × xs ≡ xs' ++ y ∷ z ∷ xs₀)
     ⊎ xs' ≡ xs × y ≡ x × z ∷ ys' ≡ ys
     ⊎ ys' ≡ ys × z ≡ x × xs ≡ xs' ++ y ∷ []
cases++2 xs xs' ys ys' {y = y}{z} r with cases++ xs xs' ys (y ∷ z ∷ ys') r
cases++2 xs ._ ._ ys' refl | inj₁ (xs₀ , refl , refl) = inj₁ (xs₀ , refl , refl)     
cases++2 ._ xs' ys ys' r | inj₂ (xs₀ , p , refl) with cases∷ xs₀ p
cases++2 ._ xs' ._ ys' r | inj₂ (.[] , refl , refl) | inj₁ (refl , refl , refl) =
  inj₂ (inj₂ (inj₁ (refl , refl , refl)))     
cases++2 ._ xs' ys ys' r | inj₂ (._ , p , refl) | inj₂ (xs₀ , s , refl) with cases∷ xs₀ s
cases++2 ._ xs' ys .ys r | inj₂ (._ , refl , refl) | inj₂ (.[] , _ , refl) | inj₁ (refl , refl , _) =
  inj₂ (inj₂ (inj₂ (refl , refl , refl)))     
cases++2 ._ xs' ys ._ r | inj₂ (._ , _ , refl) | inj₂ (._ , _ , refl) | inj₂ (xs₀ , refl , refl) = inj₂ (inj₁ (xs₀ , refl , refl))     

canc⊥ : {A : Set}{x : A}(xs ys : List A)
  → ys ≡ x ∷ xs ++ ys → ⊥
canc⊥ _ [] ()
canc⊥ [] (y ∷ ys) ()
canc⊥ (x ∷ xs) (y ∷ ys) p with inj∷ p
... | (refl , q) = canc⊥ (xs ++ y ∷ []) ys q

canc⊥2 : {A : Set}{x : A}(xs : List A){ys : List A}
  → xs ≡ xs ++ x ∷ ys → ⊥
canc⊥2 [] ()
canc⊥2 (x ∷ xs) p = canc⊥2 xs (proj₂ (inj∷ p))

canc⊥3 : {A : Set}{x : A}(xs ys zs : List A)
  → ys ≡ zs ++ x ∷ xs ++ ys → ⊥
canc⊥3 xs ys [] p = canc⊥ xs ys p
canc⊥3 {_} {x} xs ys (z ∷ zs) p = canc⊥ (zs ++ x ∷ xs) ys p

canc⊥4 : {A : Set}{x : A}(xs : List A){ys zs : List A}
  → xs ≡ (xs ++ zs) ++ x ∷ ys → ⊥
canc⊥4 [] {_}{zs} p = []disj∷ zs p
canc⊥4 (x ∷ xs) {zs = zs} p = canc⊥4 xs {zs = zs} (proj₂ (inj∷ p))

canc++ : {A : Set}(xs xs' : List A){ys : List A} → xs ++ ys ≡ xs' ++ ys → xs ≡ xs'
canc++ [] [] p = refl
canc++ [] (x ∷ xs') {ys} p = ⊥-elim (canc⊥ xs' ys p)
canc++ (x ∷ xs) [] {ys} p = ⊥-elim (canc⊥ xs ys (sym p))
canc++ (x ∷ xs) (x₁ ∷ xs') p with inj∷ p
canc++ (x ∷ xs) (.x ∷ xs'){ys} p | refl , q = cong (_∷_ x) (canc++ xs xs' {ys} q)

++canc : {A : Set}{xs xs' : List A}(ys : List A) → ys ++ xs ≡ ys ++ xs' → xs ≡ xs'
++canc [] p = p
++canc (x ∷ ys) p = ++canc ys (proj₂ (inj∷ p))

cases++-inj₁ : {X : Set} → (xs ys zs : List X) → (x : X) →
  cases++ xs (xs ++ x ∷ ys) (ys ++ zs) zs refl ≡ inj₁ (ys , refl , refl)
cases++-inj₁ xs ys zs x with cases++ xs (xs ++ x ∷ ys) (ys ++ zs) zs refl
cases++-inj₁ xs ys zs x | inj₁ (xs' , p , q) with canc++ ys xs' {zs} q
cases++-inj₁ xs ys zs x | inj₁ (.ys , refl , refl) | refl = refl
cases++-inj₁ xs ys zs x | inj₂ (ys' , p , q) = ⊥-elim (canc⊥3 ys zs ys' p)

cases++-inj₂ : {X : Set} → (xs xs' ys : List X) → (x : X) → 
   cases++ (xs' ++ xs) xs' ys (xs ++ x ∷ ys) refl ≡ inj₂ (xs , refl , refl)
cases++-inj₂ xs xs' ys x with cases++ (xs' ++ xs) xs' ys (xs ++ x ∷ ys) refl
cases++-inj₂ xs xs' ys x | inj₁ (xs₀ , p , q) = ⊥-elim (canc⊥3 [] ys (xs₀ ++ xs) q)
cases++-inj₂ xs xs' ys x | inj₂ (xs₀ , p , q) with ++canc {xs = xs}{xs₀} xs' q
cases++-inj₂ xs xs' ys x | inj₂ (.xs , refl , refl) | refl = refl

++? : {X : Set} → (xs xs' ys ys' : List X) →  
   xs' ++ ys' ≡ xs ++ ys → 
        Σ (List X) (λ xs₀ → ys' ≡ xs₀ ++ ys × xs ≡ xs' ++ xs₀) 
     ⊎ (Σ X λ x → Σ (List X) (λ xs₀ → xs' ≡ xs ++ x ∷ xs₀ × ys ≡ x ∷ xs₀ ++ ys'))
++? xs [] ys .(xs ++ ys) refl = inj₁ (xs , refl , refl) 
++? [] (x ∷ xs') .((x ∷ xs') ++ ys') ys' refl = inj₂ (x , xs' , refl , refl)
++? (x₁ ∷ xs) (x ∷ xs') ys ys' eq with inj∷ eq
... | (refl , q) with ++? xs xs' ys ys' q
... | inj₂ (y , xs₀ , refl , refl) = inj₂ (y , xs₀ , refl , refl)
... | inj₁ (xs₀ , refl , refl) = inj₁ (xs₀ , refl , refl)

++?-eq₁ : {X : Set} (zs zs' xs' : List X)
    → ++? (zs ++ zs') zs xs' (zs' ++ xs') refl ≡ inj₁ (zs' , refl , refl)
++?-eq₁ [] zs' xs' = refl
++?-eq₁ (x ∷ zs) zs' xs' rewrite ++?-eq₁ zs zs' xs' = refl

++?-eq₂ : {X : Set} (x : X) (xs zs zs' : List X)
    → ++? xs (xs ++ x ∷ zs) (x ∷ zs ++ zs') zs' refl ≡ inj₂ (x , zs , refl , refl)
++?-eq₂ x [] zs zs' = refl
++?-eq₂ x (x' ∷ xs) zs zs' rewrite ++?-eq₂ x xs zs zs' = refl

++?-alt : {X : Set} → (xs xs' ys ys' : List X) →  
   xs' ++ ys' ≡ xs ++ ys → 
        Σ (List X) (λ xs₀ → xs' ≡ xs ++ xs₀ × ys ≡ xs₀ ++ ys') 
     ⊎ (Σ X λ x → Σ (List X) (λ xs₀ → xs ≡ xs' ++ x ∷ xs₀ × ys' ≡ x ∷ xs₀ ++ ys))
++?-alt xs xs' ys ys' eq with ++? xs xs' ys ys' eq
... | inj₁ ([] , refl , refl) = inj₁ ([] , refl , refl)
... | inj₁ (x ∷ xs₀ , refl , refl) = inj₂ (x , xs₀ , refl , refl)
... | inj₂ (y , xs₀ , refl , refl) = inj₁ (y ∷ xs₀ , refl , refl)

++?-inj₁ : {X : Set} (xs₀ xs' ys : List X) →
           ++? (xs' ++ xs₀) xs' ys (xs₀ ++ ys) refl ≡ inj₁ (xs₀ , refl , refl)
++?-inj₁ xs₀ xs' ys with ++? (xs' ++ xs₀) xs' ys (xs₀ ++ ys) refl
++?-inj₁ xs₀ xs' ys | inj₁ (zs , p , q) with canc++ xs₀ zs {ys} p
++?-inj₁ xs₀ xs' ys | inj₁ (.xs₀ , refl , refl) | refl = refl
++?-inj₁ xs₀ xs' ys | inj₂ (y , zs , p , q) = ⊥-elim (canc⊥ (zs ++ xs₀) ys q)

++?-inj₂ : {X : Set} (xs xs₀ ys' : List X) (x : X) →
           ++? xs (xs ++ x ∷ xs₀) (x ∷ xs₀ ++ ys') ys' refl ≡ inj₂ (x , xs₀ , refl , refl)
++?-inj₂ xs xs₀ ys' x with ++? xs (xs ++ x ∷ xs₀) (x ∷ xs₀ ++ ys') ys' refl
... | inj₁ (zs , p , q) = ⊥-elim (canc⊥2 xs {xs₀ ++ zs} q)
... | inj₂ (y , zs , p , q) with ++canc {xs = x ∷ xs₀} {y ∷ zs} xs p
++?-inj₂ xs xs₀ ys' x | inj₂ (.x , .xs₀ , refl , refl) | refl = refl

concat++ : {A : Set} (xss yss : List (List A))
  → concat (xss ++ yss) ≡ concat xss ++ concat yss
concat++ [] yss = refl
concat++ (xs ∷ xss) yss = cong (xs ++_) (concat++ xss yss)


++[] : {A : Set} (xs ys : List A) → xs ++ ys ≡ [] → xs ≡ [] × ys ≡ []
++[] [] ys eq = refl , eq

map-concat : {A B : Set} (f : A → B) (xss : List (List A))
  → concat (map (map f) xss) ≡ map f (concat xss)
map-concat f [] = refl
map-concat f (xs ∷ xss) = cong (map f xs ++_) (map-concat f xss)

split-map : {A B : Set} (f : A → B) (xs : List A) (ys zs : List B)
  → map f xs ≡ ys ++ zs
  → Σ (List A) λ ys' → Σ (List A) λ zs' → map f ys' ≡ ys × map f zs' ≡ zs × xs ≡ ys' ++ zs'
split-map f [] [] .(map f []) refl = [] , [] , refl , refl , refl
split-map f (x ∷ xs) [] (.(f x) ∷ .(map f xs)) refl = [] , x ∷ xs , refl , refl , refl
split-map f (x ∷ xs) (y ∷ ys) zs eq with inj∷ eq
... | refl , eq' with split-map f xs ys zs eq'
... | ys' , zs' , refl , refl , refl = x ∷ ys' , zs' , refl , refl , refl

split-map-eq : {A B : Set} (f : A → B) (ys zs : List A)
  → split-map f (ys ++ zs) (map f ys) (map f zs) refl ≡ (ys , zs , refl , refl , refl)
split-map-eq f [] [] = refl
split-map-eq f [] (x ∷ zs) = refl
split-map-eq f (x ∷ ys) zs rewrite split-map-eq f ys zs = refl

snoc? : {A : Set} (xs : List A) → xs ≡ [] ⊎ Σ (List A) λ xs' → Σ A λ x → xs ≡ xs' ∷ʳ x
snoc? [] = inj₁ refl
snoc? (x ∷ xs) with snoc? xs
... | inj₁ refl = inj₂ ([] , x , refl)
... | inj₂ (xs' , x' , refl) = inj₂ (x ∷ xs' , x' , refl)

split-map++ : {X Y : Set} {f : X → Y}
  → (ys ys' : List Y) (xs xs' : List X) 
  → ys ++ ys' ≡ map f (xs ++ xs')
  → (Σ (List X) λ zs → Σ (List X) λ zs' → ys' ≡ map f (zs' ++ xs') × xs ≡ zs ++ zs' × ys ≡ map f zs)
     ⊎ (Σ X λ x → Σ (List X) λ zs → Σ (List X) λ zs' → ys ≡ map f (xs ++ x ∷ zs) × xs' ≡ x ∷ zs ++ zs' × ys' ≡ map f zs')
split-map++ {f = f} ys ys' xs xs' eq with ++? (map f xs) ys (map f xs') ys' eq
... | inj₁ (ws , refl , r) with split-map f xs ys ws r
... | (zs , zs' , refl , refl , refl) = inj₁ (zs , zs' , refl , refl , refl)
split-map++ {f = f} ._ ys' xs xs' eq | inj₂ (y , ws , refl , r) with split-map f xs' (y ∷ ws) ys' r
... | (_ ∷ zs , zs' , refl , refl , refl) = inj₂ (_ , zs , zs' , refl , refl , refl)


split-map++-alt : {X Y : Set} {f : X → Y}
  → (ys ys' : List Y) (xs xs' : List X) 
  → ys ++ ys' ≡ map f (xs ++ xs')
  → (Σ (List X) λ zs → Σ (List X) λ zs' → ys ≡ map f (xs ++ zs) × xs' ≡ zs ++ zs' × ys' ≡ map f zs')
     ⊎ (Σ X λ x → Σ (List X) λ zs → Σ (List X) λ zs' → ys' ≡ map f (x ∷ zs' ++ xs') × xs ≡ zs ++ x ∷ zs' × ys ≡ map f zs)
split-map++-alt ys ys' xs xs' eq with split-map++ ys ys' xs xs' eq
... | inj₁ (zs , [] , refl , refl , refl) = inj₁ ([] , xs' , refl , refl , refl)
... | inj₁ (zs , x ∷ zs' , refl , refl , refl) = inj₂ (x , zs , zs' , refl , refl , refl)
... | inj₂ (x , zs , zs' , refl , refl , refl) = inj₁ (x ∷ zs , zs' , refl , refl , refl)


split-map++₂ : {X Y : Set} {f : X → Y}
  → (ys ys' ys'' : List Y) (xs xs' : List X) 
  → ys ++ ys' ++ ys'' ≡ map f (xs ++ xs')
  → (Σ (List X) λ zs → Σ (List X) λ ws → Σ (List X) λ ws' → ys'' ≡ map f (ws' ++ xs') × ys' ≡ map f ws × xs ≡ zs ++ ws ++ ws' × ys ≡ map f zs)
     ⊎ (Σ (List X) λ zs → Σ (List X) λ zs' → Σ X λ x → Σ (List X) λ ws → Σ (List X) λ ws' → ys' ≡ map f (zs' ++ x ∷ ws) × xs' ≡ x ∷ ws ++ ws' × ys'' ≡ map f ws' × xs ≡ zs ++ zs' × ys ≡ map f zs)
     ⊎ (Σ X λ x → Σ (List X) λ zs → Σ (List X) λ zs' → Σ (List X) λ zs'' → ys ≡ map f (xs ++ x ∷ zs) × xs' ≡ x ∷ zs ++ zs' ++ zs'' × ys' ≡ map f zs' × ys'' ≡ map f zs'')
split-map++₂ ys ys' ys'' xs xs' eq with split-map++ ys (ys' ++ ys'') xs xs' eq
... | inj₁ (zs , zs' , p , q , r) with split-map++ ys' ys'' zs' xs' p
... | inj₁ (ws , ws' , p' , refl , r') = inj₁ (zs , ws , ws' , p' , r' , q , r)
... | inj₂ (x , ws , ws' , p' , q' , r') = inj₂ (inj₁ (zs , zs' , x , ws , ws' , p' , q' , r' , q , r))
split-map++₂ {f = f} ys ys' ys'' xs xs' eq | inj₂ (x , zs , ws , p , q , r) with split-map f ws ys' ys'' (sym r)
... | (zs' , zs'' , p' , q' , refl) = inj₂ (inj₂ (x , zs , zs' , zs'' , p , q , sym p' , sym q'))

split-map++₂-alt : {X Y : Set} {f : X → Y}
  → (ys ys' ys'' : List Y) (xs xs' : List X) 
  → ys ++ ys' ++ ys'' ≡ map f (xs ++ xs')
  → (Σ (List X) λ zs → Σ (List X) λ zs' → Σ (List X) λ zs'' → ys ≡ map f (xs ++ zs) × ys' ≡ map f zs' × xs' ≡ zs ++ zs' ++ zs'' × ys'' ≡ map f zs'')
     ⊎ (Σ (List X) λ zs → Σ (List X) λ zs' → Σ X λ x → Σ (List X) λ ws → Σ (List X) λ ws' → ys' ≡ map f (x ∷ ws' ++ zs) × xs ≡ ws ++ x ∷ ws' × ys ≡ map f ws × xs' ≡ zs ++ zs' × ys'' ≡ map f zs')
     ⊎ (Σ X λ x → Σ (List X) λ zs → Σ (List X) λ zs' → Σ (List X) λ zs'' → ys'' ≡ map f (x ∷ zs'' ++ xs') × xs ≡ zs ++ zs' ++ x ∷ zs'' × ys ≡ map f zs × ys' ≡ map f zs')
split-map++₂-alt {f = f} ys ys' ys'' xs xs' eq with split-map++-alt (ys ++ ys') ys'' xs xs' eq
... | inj₁ (zs , zs' , p , q , r) with split-map++-alt ys ys' xs zs p
... | inj₁ (ws , ws' , p' , refl , r') = inj₁ (ws , ws' , zs' , p' , r' , q , r)
... | inj₂ (x , ws , ws' , p' , q' , r') = inj₂ (inj₁ (zs , zs' , x , ws , ws' , p' , q' , r' , q , r))
split-map++₂-alt {f = f} ys ys' ys'' xs xs' eq | inj₂ (x , zs , zs' , p , q , r) with split-map f zs ys ys' (sym r)
... | zs₀ , zs₁ , p' , q' , refl = inj₂ (inj₂ (x , zs₀ , zs₁ , zs' , p , q , sym p' , sym q'))

split-map++-eq₁ : {X Y : Set} (f : X → Y)
  → (zs zs' xs' : List X)
  → split-map++ {f = f} (map f zs) (map f (zs' ++ xs')) (zs ++ zs') xs' refl
                ≡ inj₁ (zs , zs' , refl , refl , refl)
split-map++-eq₁ f zs zs' xs' rewrite ++?-eq₁ (map f zs) (map f zs') (map f xs') | split-map-eq f zs zs' = refl

split-map++-eq₂ : {X Y : Set} (f : X → Y)
  → (x : X) (xs zs zs' : List X)
  → split-map++ {f = f} (map f (xs ++ x ∷ zs)) (map f zs') xs (x ∷ zs ++ zs') refl
                ≡ inj₂ (x , zs , zs' , refl , refl , refl)
split-map++-eq₂ f x xs zs zs' rewrite ++?-eq₂ (f x) (map f xs) (map f zs) (map f zs') | split-map-eq f zs zs' = refl

postulate 
  split-map++-alt-eq₁ : {X Y : Set} (f : X → Y)
    → (zs xs zs' : List X)
    → split-map++-alt {f = f} (map f (zs ++ xs)) (map f zs') zs (xs ++ zs') refl
            ≡ inj₁ (xs , zs' , refl , refl , refl)
    
  split-map++-alt-eq₂ : {X Y : Set} (f : X → Y)
    → (x : X) (zs zs' xs' : List X)
    → split-map++-alt {f = f} (map f zs) (map f (x ∷ zs' ++ xs')) (zs ++ x ∷ zs') xs' refl
                      ≡ inj₂ (x , zs , zs' , refl , refl , refl)


open import Data.List.Relation.Unary.All hiding (map)

-- Append for All

_++All_ : {A : Set} {P : A → Set}
  → {xs ys : List A} 
  → All P xs → All P ys → All P (xs ++ ys)
[] ++All qs = qs
(px ∷ ps) ++All qs = px ∷ (ps ++All qs)

snocAll : {A : Set} {P : A → Set}
  → {xs : List A} {x : A}
  → All P xs → P x → All P (xs ∷ʳ x)
snocAll ps p = ps ++All p ∷ []

infixr 5 _++All_

