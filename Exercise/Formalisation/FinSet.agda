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

-- lb = {2, 2, 1}

lb : List ℕ
lb = 2 , f
  where
    f : Fin 3 → ℕ
    f zero = 2
    f (suc zero) = 2
    f (suc (suc i)) = 1

la~lb : la ~ lb
la~lb = (φ1 , p1) , φ2 , p2
  where
    φ1 : Fin 2 → Fin 3
    φ1 zero = suc zero
    φ1 (suc i) = zero

    

    p1 : ∀ (n : Fin 2) →
           (proj₂ lb) (φ n) ≡ (proj₂ la) n
    p1 zero = refl
    p1 (suc i) = refl

    
    p2 : ∀ (n : Fin 2) →
           (proj₂ la) (φ n) ≡ (proj₂ lb) n
    p2 zero = refl
    p2 (suc i) = refl