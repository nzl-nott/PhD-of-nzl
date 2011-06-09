module FinSet where

open import Data.Product
open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality

Rel : (A : Set) → Set₁
Rel A = A → A → Set

-- Finite sets

List : Set → Set
List A = Σ[ n ∶ ℕ ] (Fin n → A)

_⊆_ : {A : Set} → List A → List A → Set
(m , f) ⊆ (n , g) = 
  ∃ λ (φ : Fin m → Fin n) → 
   (x : Fin m) → g (φ x) ≡ f x

_~_ : {A : Set} → Rel (List A)
mf ~ ng = mf ⊆ ng × ng ⊆ mf

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