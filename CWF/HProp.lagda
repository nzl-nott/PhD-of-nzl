\begin{code}

open import Level
open import Relation.Binary.PropositionalEquality

module HProp (ext : Extensionality zero zero) where

open import Relation.Nullary
open import Data.Unit
open import Data.Empty
open import Data.Nat

\end{code}

HProp as propositional universe

\begin{code}

record HProp : Set₁ where
  constructor hProp
  field
    prf : Set
    Uni : {p q : prf} → p ≡ q

open HProp public renaming (prf to <_>)


⊤' : HProp
⊤' = hProp ⊤ refl

exUni : {A : Set} → (∀ (p q : A) → p ≡ q) → (∀ {p q : A} → p ≡ q)
exUni f {p} {q} = f p q

⊥' : HProp
⊥' = hProp ⊥ (exUni (λ ()))

\end{code}

HProp is closed under Π-types

1. universal quantification

\begin{code}

∀' : (A : Set)(P : A → HProp) → HProp
∀' A P = hProp ((x : A) → < P x >) (ext (λ x → Uni (P x)))

syntax ∀' A (λ x → B) = ∀'[ x ∶ A ] B

infixr 2 _⇛_

_⇛_ : (P Q : HProp) → HProp
P ⇛ Q =  ∀' < P > (λ _ → Q)

\end{code}

HProp is closed under Σ-types

\begin{code}

open import Data.Product

sig-eq : {A : Set}{B : A → Set}{a b : A} → (p : a ≡ b) → {c : B a}{d : B b} → (subst (λ x → B x) p c ≡ d) → _≡_ {_} {Σ A B} (a , c) (b , d)
sig-eq refl refl = refl

Σ' : (P : HProp)(Q : < P > → HProp) → HProp
Σ' P Q = hProp (Σ < P > (λ x → < Q x >)) (λ {p} {q} → sig-eq (Uni P) (Uni (Q (proj₁ q))))


syntax Σ' A (λ x → B) = Σ'[ x ∶ A ] B

infixr 3 _∧_

_∧_ : (P Q : HProp) → HProp
P ∧ Q = Σ' P (λ _ → Q)

\end{code}

Negation

\begin{code}

~ : HProp → HProp
~ P = P ⇛ ⊥' 

\end{code}

Logical equivalence

\begin{code}

_⇄_   : (P Q : HProp) → HProp
P ⇄ Q = (P ⇛ Q) ∧ (Q ⇛ P)

\end{code}