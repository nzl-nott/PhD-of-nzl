module HProp where

open import Relation.Binary.PropositionalEquality

record HProp : Set₁ where
  constructor hProp
  field
    <_> : Set
    Uni : (p q : <_>) → p ≡ q

open HProp public

--SquashSet

record SquashSet (A : Set) : Set where
   constructor ss
   field
     .proof : A


pirr : {P : Set}(p q : SquashSet P) → p ≡ q
pirr (ss p) (ss p') = refl

-- HProp is closed under Π-types

Π : {A : Set}(P : A → HProp) → HProp
Π {A} P = hProp ((x : A) → SquashSet < P x >) (λ p q → refl)


app : {A : Set}{P : A → HProp} → < Π {A} P > → (x : A) → < P x >
app f x = {!!}

infixr 2 _⇛_

_⇛_ : (P Q : HProp) → HProp
P ⇛ Q = Π {< P >} (λ _ → Q)

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

-- squash

⟦_⟧ : Set → HProp
⟦ A ⟧ = hProp (SquashSet A) pirr

