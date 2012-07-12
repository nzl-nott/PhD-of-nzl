open import Level
open import Relation.Binary.PropositionalEquality as PE hiding (sym ; trans; isEquivalence)

module HProp1 (ext : Extensionality zero zero) where

open import Relation.Nullary
open import Data.Unit
open import Data.Empty
open import Data.Nat

---------------------------------
-- 1. HProp

record HProp : Set₁ where
  constructor hProp
  field
    <_> : Set
    Uni : {p q : <_>} → p ≡ q

open HProp public

-- basic propositions

⊤' : HProp
⊤' = hProp ⊤ refl

exUni : {A : Set} → (∀ (p q : A) → p ≡ q) → (∀ {p q : A} → p ≡ q)
exUni f {p} {q} = f p q

⊥' : HProp
⊥' = hProp ⊥ (exUni (λ ()))

-------------------------------------
-- HProp is closed under Π-types
-- universal quantification

∀' : (A : Set)(P : A → HProp) → HProp
∀' A P = hProp ((x : A) → < P x >) (ext (λ x → Uni (P x)))

syntax ∀' A (λ x → B) = ∀[ x ∶ A ] B

-- independent version is implication

infixr 2 _⇛_

_⇛_ : (P Q : HProp) → HProp
P ⇛ Q =  ∀' < P > (λ _ → Q)



open import Data.Product

sig-eq : {A : Set}{B : A → Set}{a b : A} → (p : a ≡ b) → {c : B a}{d : B b} → (subst (λ x → B x) p c ≡ d) → _≡_ {_} {Σ A B} (a , c) (b , d)
sig-eq refl refl = refl


-------------------------------------
-- HProp is closed under Σ-types

Σ' : (P : HProp)(Q : < P > → HProp) → HProp
Σ' P Q = hProp (Σ < P > (λ x → < Q x >)) (λ {p} {q} → sig-eq (Uni P) (Uni (Q (proj₁ q))))

-- independent version is conjunction

infixr 3 _∧_

_∧_ : (P Q : HProp) → HProp
P ∧ Q = Σ' P (λ _ → Q)

-- negation

~ : HProp → HProp
~ P = P ⇛ ⊥' 

-- equivalent relation

_⇄_   : (P Q : HProp) → HProp
P ⇄ Q = (P ⇛ Q) ∧ (Q ⇛ P)

