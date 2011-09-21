module EpiSplit where

open import Data.Product
open import Relation.Nullary
open import Data.Bool hiding (_∨_)
open import Data.Empty

-- prove classically all epi are split

data _≡_ {A : Set}(a : A) : A → Set where
     refl : a ≡ a

subst : {A : Set}(P : A → Set)(a b : A) → a ≡ b → P a → P b
subst P .b b refl y = y

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

postulate classic : (P : Set) → P ∨ (¬ P)



sym : ∀ {A}{a b : A} → a ≡ b → b ≡ a
sym refl = refl

assoc : ∀ {A}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
assoc refl refl = refl

Epi : {A B : Set} → (e : A → B) → (C : Set) → Set
Epi {A} {B} e C =
      ∀ (f g : B → C) →
      (∀ (a : A) → f (e a) ≡ g (e a)) →
      ∀ (b : B) → f b ≡ g b


Surjective : {A B : Set} → (e : A → B) → Set
Surjective {A} {B} e = ∀ (b : B) → ∃ (λ a → e a ≡ b)

Split : {A B : Set} → (e : A → B) → Set
Split {A} {B} e = ∃ λ (s : B → A) → ∀ b → e (s b) ≡ b

Surj→Split : ∀ A B e → Surjective {A} {B} e → Split e
Surj→Split a B e split = (λ x → proj₁ (split x)) , λ b' → proj₂ (split b')

Epi→Split : {A B : Set} → (e : A → B) → Set₁
Epi→Split e = ((C : Set) → Epi e C) → Split e

-- assume we have an epi e

postulate A B : Set
postulate e : A → B

-- assume e is not split

postulate ¬split : ¬ Split e

postulate DeMorgan : ∀ {A : Set}{P : A → Set} → ¬ (∀ (x : A) → P x) → ∃ λ (x : A) → ¬ P x

¬surj : ∃ λ b → ¬ (∃ λ (a : A) → (e a ≡ b))
¬surj = DeMorgan (λ x → ¬split ((λ b → proj₁ (x b)) , λ b → (proj₂ (x b))))

b = proj₁ ¬surj

ignore : ∀ (a : A) → ¬ (e a ≡ b)
ignore a eq = proj₂ ¬surj (a , eq)

f : B → Bool
f x = false

postulate g : B → Bool
postulate gb : g b ≡ true
postulate gb' : ∀ b' → ¬ (b' ≡ b) → false ≡ g b'


¬epiBool : ¬ Epi e Bool
¬epiBool epi with assoc (epi f g (λ a → gb' (e a) (ignore a)) b) gb
... | ()

¬epi : ¬ (∀ C → Epi e C) 
¬epi epi = ¬epiBool (epi Bool)


raa : {P : Set} → ¬ (¬ P) → P
raa {P} nnp with classic P
raa nnp | inl y = y
raa nnp | inr y with nnp y
... | ()

contrapositive : ∀ {P Q : Set} → (¬ Q → ¬ P) → P → Q
contrapositive nqnp p = raa (λ nq → nqnp nq p)














{-


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

-}