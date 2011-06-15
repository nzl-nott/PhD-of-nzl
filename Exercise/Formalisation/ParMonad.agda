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

-}