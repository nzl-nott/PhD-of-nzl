module ParMonad where

open import Coinduction
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality


-- Equivalence relation

Rel : (A : Set) → Set₁
Rel A = A → A → Set

-- Finite sets

data _⊥₀ (A : Set) : Set where
  now   : A → A ⊥₀
  later : ∞ A ⊥₀ → A ⊥₀

prop = Set


-- Why not now⊑ : {a : A} → 
--            now a ⊑ now a

data _⊑_ {A : Set} : A ⊥₀ → A ⊥₀ → prop where
  now⊑      : {a a' : A} → 
              now a ⊑ now a'
  later⊑    : {d d' : ∞ A ⊥₀} → 
              ∞ (d ⊑ d') → later d ⊑ later d'
  laterLeft : {d : ∞ A ⊥₀}{d' : A ⊥₀} →
              later d ⊑ d'

_~_ : {A : Set} → Rel (A ⊥₀)
d ~ d' = d ⊑ d' × d' ⊑ d


{-
-- example 

-- la = {1, 2}

la : List ℕ
la = 2 , f
  where
    f : Fin 2 → ℕ
    f zero = 1
    f (suc i) = 2

-- lb = {2, 1}

lb : List ℕ
lb = 2 , f
  where
    f : Fin 2 → ℕ
    f zero = 2
    f (suc i) = 1

la~lb : la ~ lb
la~lb = (φ , perm1) , φ , perm2
  where
    φ : Fin 2 → Fin 2
    φ zero = suc zero
    φ (suc i) = zero

    perm1 : ∀ (n : Fin 2) →
           (proj₂ lb) (φ n) ≡ (proj₂ la) n
    perm1 zero = refl
    perm1 (suc i) = refl

    
    perm2 : ∀ (n : Fin 2) →
           (proj₂ la) (φ n) ≡ (proj₂ lb) n
    perm2 zero = refl
    perm2 (suc i) = refl

-}