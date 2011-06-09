module FinMulSet where

open import Data.Product
open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality


Rel : (A : Set) → Set₁
Rel A = A → A → Set

-- Finite multisets

List : Set → Set
List A = Σ[ n ∶ ℕ ] (Fin n → A)


Surjection : {A B : Set} → (φ : A → B) → Set
Surjection {A} {B} φ = ∃ λ (ψ : B → A) →
                       ∀ (b : B) → φ (ψ b) ≡ b


_~_ : {A : Set} → Rel (List A)
(m , f) ~ (n , g) = 
  ∃ λ (φ : Fin m → Fin n) → 
      Surjection φ ×
      ((x : Fin m) → g (φ x) ≡ f x)

-- example 

-- la = {2, 1, 2}

la : List ℕ
la = 3 , f
  where
    f : Fin 3 → ℕ
    f zero = 2
    f (suc zero) = 1
    f (suc (suc i)) = 2

-- lb = {1, 2}

lb : List ℕ
lb = 2 , f
  where
    f : Fin 2 → ℕ
    f zero = 1
    f (suc i) = 2

la~lb : la ~ lb
la~lb = φ , (ψ , surj) , perm
  where
    φ : Fin 3 → Fin 2
    φ zero = suc zero
    φ (suc zero) = zero
    φ (suc (suc i)) = suc zero

    ψ : Fin 2 → Fin 3
    ψ zero = suc zero
    ψ (suc i) = zero

    surj : ∀ (n : Fin 2) → φ (ψ n) ≡ n
    surj zero = refl
    surj (suc zero) = refl
    surj (suc (suc ()))

    perm : ∀ (n : Fin 3) →
           (proj₂ lb) (φ n) ≡ (proj₂ la) n
    perm zero = refl
    perm (suc zero) = refl
    perm (suc (suc i)) = refl

