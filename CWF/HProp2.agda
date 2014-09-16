open import Level
open import Relation.Binary.PropositionalEquality

module HProp2 where

open import Relation.Nullary
-- open import Data.Unit
-- open import Data.Empty
open import Data.Nat




data Prop' : Set₁ where
  ⊤ ⊥ : Prop'
  ∀' : (A : Set)(P : A → Prop') → Prop'
  Σ' : (A : Prop')(P : A → Prop') → Prop'

{-

---------------------------------
-- 1. Prop'

postulate Prop' : Set₁

postulate ∣_∣ : Prop' → Set

-- basic propositions

postulate ⊤ ⊥ : Prop'

postulate ⊥-elim : {A : Set} → ∣ ⊥ ∣ → A

-------------------------------------
-- Prop' is closed under Π-types
-- universal quantification

postulate ∀' : (A : Set)(P : A → Prop') → Prop'

syntax ∀' A (λ x → B) = ∀'[ x ∶ A ] B

postulate lam : {A : Set}{P : A → Prop'} → (a : A) → ∣ P a ∣ →  ∣ ∀' A P ∣ 

postulate app : {A : Set}{B : Prop'} → ∣ ∀' A (λ x → B) ∣ → A → ∣ B ∣

postulate app-β : {A : Set}{P : A → Prop'}{a : A}{t : ∣ P a  ∣}{b : A} → app (lam a t) b ≡ t



-------------------------------------
-- Prop' is closed under Σ-types
-- Existential quantification

postulate Σ' : (A : Prop')(P : ∣ A ∣ → Prop') → Prop'

syntax  Σ' A (λ x → B) = Σ'[ x ∶ A ] B

postulate _,_ : {A : Prop'}{P : ∣ A ∣ → Prop'} → (a : ∣ A ∣) → ∣ P a ∣ →  ∣ Σ' A P ∣ 

postulate fst : {A : Set}{B : Prop'} → ∣ ∀' A (λ x → B) ∣ → A → ∣ B ∣

postulate snd : {A : Set}{B : Prop'} → ∣ ∀' A (λ x → B) ∣ → A → ∣ B ∣

postulate pair-β : {A : Set}{P : A → Prop'}{a : A}{t :  ∣ P a ∣}{b : A} → app (lam a t) b ≡ t
-}