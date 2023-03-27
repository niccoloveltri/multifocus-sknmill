{-# OPTIONS --rewriting #-}

module Formulae where

open import Data.Maybe
open import Data.List
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Utilities

postulate At : Set

-- Formulae
data Fma : Set where
  ` : At → Fma
  I : Fma
  _⊗_ : Fma → Fma → Fma
  _⊸_ : Fma → Fma → Fma

infix 22 _⊸_ _⊗_

-- Stoup
Stp : Set
Stp = Maybe Fma

pattern ─ = nothing

-- Context
Cxt : Set
Cxt = List Fma

-- Iterated ⊗
_⊗⋆_ : Fma → Cxt → Fma
A ⊗⋆ [] = A
A ⊗⋆ (B ∷ Γ) = (A ⊗ B) ⊗⋆ Γ

-- Iterated ⊸
_⊸⋆_ : Cxt → Fma → Fma
[] ⊸⋆ C = C
(A ∷ Γ) ⊸⋆ C = A ⊸ (Γ ⊸⋆ C)

infix 21 _⊗⋆_
infix 21 _⊸⋆_

-- ⊗⋆ and ⊸⋆ are monoid action on contexts
++⊗⋆ : (A : Fma) (Γ Γ' : Cxt)
  → A ⊗⋆ (Γ ++ Γ') ≡ (A ⊗⋆ Γ) ⊗⋆ Γ'
++⊗⋆ A [] Γ' = refl
++⊗⋆ A (B ∷ Γ) Γ' = ++⊗⋆ (A ⊗ B) Γ Γ'

++⊸⋆ : (Γ Γ' : Cxt) (B : Fma)
  → (Γ ++ Γ') ⊸⋆ B ≡ Γ ⊸⋆ (Γ' ⊸⋆ B)
++⊸⋆ [] Γ' B = refl
++⊸⋆ (x ∷ Γ) Γ' B = cong (x ⊸_) (++⊸⋆ Γ Γ' B)

{-# REWRITE ++⊗⋆ #-}
{-# REWRITE ++⊸⋆ #-}

-- Predicates on formulae checking whether:

-- -- the formula isn't atomic
isn'tAt : Fma → Set
isn'tAt (` X) = ⊥
isn'tAt _ = ⊤

-- -- the formula isn't ⊗
isn't⊗ : Fma → Set
isn't⊗ (A ⊗ B) = ⊥
isn't⊗ _ = ⊤

-- -- the formula negative or atomic
isNegAt : Fma → Set
isNegAt (` X) = ⊤
isNegAt (A ⊸ B) = ⊤
isNegAt _ = ⊥

-- -- the formula is negative
is⊸ : Fma → Set
is⊸ (A ⊸ B) = ⊤
is⊸ _ = ⊥

isNeg = is⊸

-- -- the formula is atomic
isAt : Fma → Set
isAt (` X) = ⊤
isAt _ = ⊥

-- -- the formula is positive or atomic
isPosAt : Fma → Set
isPosAt (A ⊸ B) = ⊥
isPosAt _ = ⊤

-- -- the formula is positive 
isPos : Fma → Set
isPos (A ⊸ B) = ⊥
isPos (` X) = ⊥
isPos _ = ⊤

-- Predicate on stoups checking whether the stoup is irreducible,
-- i.e. if it is a single formula, then it is negative
isIrr : Stp → Set
isIrr ─ = ⊤
isIrr (just A) = isNegAt A

-- If A is positive or atomic, then A ⊗⋆ Γ is as well
isPosAt⊗⋆ : {Q : Fma} → isPosAt Q → (Γ : Cxt) → isPosAt (Q ⊗⋆ Γ)
isPosAt⊗⋆ q [] = q
isPosAt⊗⋆ q (A ∷ Γ) = isPosAt⊗⋆ _ Γ

-- If A is positive, then A ⊗⋆ Γ is as well
isPos⊗⋆ : {Q : Fma} → isPos Q → (Γ : Cxt) → isPos (Q ⊗⋆ Γ)
isPos⊗⋆ q [] = q
isPos⊗⋆ q (A ∷ Γ) = isPos⊗⋆ _ Γ

-- Relationship between polarities
neg→isn't⊗ : {A : Fma} → isNeg A → isn't⊗ A
neg→isn't⊗ {A ⊸ A₁} m = tt

neg→negat : {A : Fma} → isNeg A → isNegAt A
neg→negat {A ⊸ A₁} m = tt

negat→isn't⊗ : {A : Fma} → isNegAt A → isn't⊗ A
negat→isn't⊗ {` x} m = tt
negat→isn't⊗ {A ⊸ A₁} m = tt

neg×posat→⊥ : {A : Fma} → isNeg A → isPosAt A → ⊥
neg×posat→⊥ {` x} p q = p
neg×posat→⊥ {I} p q = p
neg×posat→⊥ {A ⊗ A₁} p q = p
neg×posat→⊥ {A ⊸ A₁} p q = q

pos×negat→⊥ : {A : Fma} → isPos A → isNegAt A → ⊥
pos×negat→⊥ {` x} p q = p
pos×negat→⊥ {I} p q = q
pos×negat→⊥ {A ⊗ A₁} p q = q
pos×negat→⊥ {A ⊸ A₁} p q = p

is⊗ : Fma → Set
is⊗ (A ⊗ B) = ⊤
is⊗ _ = ⊥

is⊗×isn't⊗→⊥ : {C : Fma} → is⊗ C → isn't⊗ C → ⊥
is⊗×isn't⊗→⊥ {` x} p q = p
is⊗×isn't⊗→⊥ {I} p q = p
is⊗×isn't⊗→⊥ {C ⊗ C₁} p q = q
is⊗×isn't⊗→⊥ {C ⊸ C₁} p q = p

is⊗⊗⋆ : {A : Fma} → is⊗ A → (Γ : Cxt) → is⊗ (A ⊗⋆ Γ)
is⊗⊗⋆ a [] = a
is⊗⊗⋆ a (B ∷ Γ) = is⊗⊗⋆ tt Γ

at→posat : {A : Fma} → isAt A → isPosAt A
at→posat {` x} p = tt

at→negat : {A : Fma} → isAt A → isNegAt A
at→negat {` x} p = tt

negat×posat→at : {A : Fma} → isNegAt A → isPosAt A → isAt A
negat×posat→at {` x} p q = tt

pos→posat : {A : Fma} → isPos A → isPosAt A
pos→posat {I} p = tt
pos→posat {A ⊗ A₁} p = tt

pos→isn'tat : {A : Fma} → isPos A → isn'tAt A
pos→isn'tat {I} p = tt
pos→isn'tat {A ⊗ A₁} p = tt

isProp-isAt : ∀ {A} (p q : isAt A) → p ≡ q
isProp-isAt {` X} p q = refl

isProp-isPosAt : ∀ {A} (p q : isPosAt A) → p ≡ q
isProp-isPosAt {` X} p q = refl
isProp-isPosAt {I} p q = refl
isProp-isPosAt {_ ⊗ _} p q = refl

isProp-isPos : ∀ {A} (p q : isPos A) → p ≡ q
isProp-isPos {I} p q = refl
isProp-isPos {_ ⊗ _} p q = refl

isProp-isn't⊗ : ∀ {A} (p q : isn't⊗ A) → p ≡ q
isProp-isn't⊗ {` X} p q = refl
isProp-isn't⊗ {I} p q = refl
isProp-isn't⊗ {_ ⊸ _} p q = refl

isProp-isNegAt : ∀ {A} (p q : isNegAt A) → p ≡ q
isProp-isNegAt {` X} p q = refl
isProp-isNegAt {_ ⊸ _} p q = refl

isProp-isIrr : {S : Stp} (s s' : isIrr S) → s ≡ s'
isProp-isIrr {just x} s s' = isProp-isNegAt s s'
isProp-isIrr {─} s s' = refl
