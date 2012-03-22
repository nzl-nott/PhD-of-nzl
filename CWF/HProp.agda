module HProp where

open import Relation.Binary.PropositionalEquality
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
    Uni : (p q : <_>) → p ≡ q

open HProp public

-- basic propositions

⊤' : HProp
⊤' = hProp ⊤ (λ p q → refl)

⊥' : HProp
⊥' = hProp ⊥ λ()

⊥e : {σ : Set} → ⊥ → σ
⊥e ()

----------------------------------
-- 2. SquashSet

record SquashSet (A : Set) : Set where
   constructor ss
   field
     .proof : A


pirr : {P : Set}(p q : SquashSet P) → p ≡ q
pirr (ss p) (ss p') = refl

-- squash

⟦_⟧ : Set → HProp
⟦ A ⟧ = hProp (SquashSet A) pirr


-------------------------------------
-- HProp is closed under Π-types
-- universal quantification

∀' : (A : Set)(P : A → HProp) → HProp
∀' A P = hProp ((x : A) → SquashSet < P x >) (λ p q → refl)

import Data.Product

syntax ∀' A (λ x → B) = ∀[ x ∶ A ] B


-- independent version is implication

infixr 2 _⇛_

_⇛_ : (P Q : HProp) → HProp
P ⇛ Q = ∀' < P > (λ _ → Q)

-- application

-- it seems that recover is necessary, whether there will be inconsistence?

postulate recover : {P : HProp} → SquashSet < P > → < P >

uni-inst : {P : HProp} → ∀ (p : < P >) → p ≡ recover {P} (ss p)
uni-inst {P} p = Uni P p (recover {P} (ss p))


squash∀ : {A : Set}{P : A → HProp} → (∀ (x : A) → < P x >) → < ∀[ x ∶ A ] P x >
squash∀ f x = ss (f x)


app-d : {A : Set}{P : A → HProp} → < ∀[ x ∶ A ] P x > →  (∀ (x : A) → < P x >)
app-d {A} {P} h x = recover {P x} (h x)

app : {P : HProp} → {Q : HProp} → < P ⇛ Q > → (x : < P >) → < Q >
app {P} {Q} f x = recover {Q} (f x)


record Σ' (A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

sig-eq : {A : Set}{B : A → Set}{a : A}{a b : A} → (p : a ≡ b) → {c : B a}{d : B b} → (subst (λ x → B x) p c ≡ d) → _≡_ {_} {Σ' A B} (a , c) (b , d)
sig-eq refl refl = refl

sig-pir : {P : HProp}{Q : < P > → HProp}(p q : Σ' < P > (λ x → < Q x >)) → p ≡ q
sig-pir {P} {Q} (fst , snd) (fst' , snd') = sig-eq {< P >} { (λ x → < Q x >)} {fst} (Uni P fst fst') (Uni (Q fst') (subst (λ x → < Q x >) (Uni P fst fst') snd) snd')

-- HProp is closed under Σ-types

Σ : (P : HProp)(Q : < P > → HProp) → HProp
Σ P Q = hProp (Σ' < P > (λ x → < Q x >)) (sig-pir {P} {Q})

-- independent version is conjunction

infixr 3 _∧_

_∧_ : (P Q : HProp) → HProp
P ∧ Q = Σ P (λ _ → Q)

-- negation

~ : HProp → HProp
~ (hProp <_> y) = hProp (<_> → SquashSet ⊥) (λ p q → refl)

~' : HProp → HProp
~' P = P ⇛ ⊥' 

_⇄_   : (P Q : HProp) → HProp
P ⇄ Q = (P ⇛ Q) ∧ (Q ⇛ P)

defeq : (P : HProp) → < (~ P) ⇄ (~' P) >
defeq P = (λ x → ss x) , λ x → ss (λ x' → x x')