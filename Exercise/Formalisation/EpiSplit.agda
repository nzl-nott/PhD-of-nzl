module EpiSplit where

open import Data.Product
open import Relation.Nullary
open import Data.Bool
open import Data.Empty

data _≡_ {A : Set}(a : A) : A → Set where
     refl : a ≡ a

Epi : {A B : Set} → (e : A → B) → (C : Set) → Set
Epi {A} {B} e C =
      ∀ (f g : B → C) →
      (∀ (a : A) → f (e a) ≡ g (e a)) →
      ∀ (b : B) → f b ≡ g b

Split : {A B : Set} → (e : A → B) → Set
Split {A} {B} e = ∀ (b : B) → ∃ (λ a → e a ≡ b)


Epi→Split = {A B : Set} →
            (e : A → B) → (C : Set) → Epi e C → Split e


fne : ∀ {X : Set}{P : X → Set} → (∀ (x : X) → ¬ (P x)) → ¬ (∃ λ (x : X) → P x)
fne P (x , px) = P x px

-- assume we have an epi e


postulate A B : Set
postulate e : A → B

-- if e is epi, then we should have a proof of it when C is Bool

postulate epi : Epi e Bool

-- assume ¬split : ∃ (b : B) → ∀ (a : A) → ¬ (b ≡ e a)

postulate b : B
postulate ignore : ∀ (a : A) → ¬ (b ≡ e a)

-- A is not empty, so classically we have at least one element a

postulate a : A


∣_∣ : ∀ {p : Set} → Dec p → Bool
∣ yes p' ∣ = true
∣ no ¬p ∣ = false

postulate ?b≡ : (x : B) → Dec (b ≡ x)

f : B → Bool
f x = false

g : B → Bool
g x = ∣ ?b≡ x ∣


⊥ft : ⊥ → false ≡ true
⊥ft ()

gb : g b ≡ true
gb with ?b≡ b
gb | yes p = refl
gb | no ¬p = ⊥ft (¬p refl)


fe=ge : ∀ (x : A) → f (e x) ≡ g (e x)
fe=ge a with ?b≡(e a)
fe=ge a | yes p = ⊥ft (ignore a p)
fe=ge a | no ¬p = refl

fnt : ¬ (false ≡ true)
fnt ()

postulate lemma : ∀ x y → x ≡ true → y ≡ x → y ≡ true

fnb : ¬ (false ≡ ∣ ?b≡ b ∣)
fnb t = fnt (lemma (g b) false gb t)

contra : ∃ λ (b' : B) → ¬ (f b ≡ g b)
contra = b , fnb

contradiction : ⊥
contradiction = fnb (epi f g fe=ge b)

postulate classic : {P : Set} → ¬ (¬ P) → P

invcom : ∀ {P Q : Set} → (¬ Q → ¬ P) → P → Q
invcom nqnp p = classic (λ nq → nqnp nq p)
