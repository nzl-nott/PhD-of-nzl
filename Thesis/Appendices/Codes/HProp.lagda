\AgdaHide{
\begin{code}

open import Level
open import Relation.Binary.PropositionalEquality

module HProp (ext : Extensionality zero zero) where

open import Relation.Nullary
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Function
open import Data.Product

\end{code}
}

\section{Metatheory}

\HProp

\begin{code}
record HProp : Set₁ where
  constructor hProp
  field
    prf : Set
    Uni : {p q : prf} → p ≡ q

open HProp public renaming (prf to <_>)
\end{code}

$\top$ and $\bot$

\begin{code}
⊤' : HProp
⊤' = hProp ⊤ refl

exUni : {A : Set} → (∀ (p q : A) → p ≡ q) 
      → (∀ {p q : A} → p ≡ q)
exUni f {p} {q} = f p q

⊥' : HProp
⊥' = hProp ⊥ (exUni (λ ()))
\end{code}

\HProp is closed under $\Pi$-types

\begin{code}
∀' : (A : Set)(P : A → HProp) → HProp
∀' A P = hProp ((x : A) → < P x >) (ext (λ x → Uni (P x)))
\end{code}

\AgdaHide{
\begin{code}
syntax ∀' A (λ x → B) = ∀'[ x ∶ A ] B
\end{code}
}

\begin{code}
infixr 2 _⇛_

_⇛_ : (P Q : HProp) → HProp
P ⇛ Q =  ∀' < P > (λ _ → Q)
\end{code}

\HProp is closed under $\Sigma$-types

\begin{code}
sig-eq : {A : Set}{B : A → Set}
         {a b : A}(p : a ≡ b)
         {c : B a}{d : B b} →
         (subst (λ x → B x) p c ≡ d) →
         _≡_ {_} {Σ A B} (a , c) (b , d)
sig-eq refl refl = refl

Σ' : (P : HProp)(Q : < P > → HProp) → HProp
Σ' P Q = hProp (Σ < P > (λ x → < Q x >)) 
         (λ {p} {q} → sig-eq (Uni P) (Uni (Q (proj₁ q))))
\end{code}

\AgdaHide{
\begin{code}
syntax Σ' A (λ x → B) = Σ'[ x ∶ A ] B
\end{code}
}

\begin{code}
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

$\eta$-rules for $\Pi$-types and $\Sigma$-types

\begin{code}
Π-eta : {A : Set}{B : A → Set}(f : (a : A) → B a) → 
        (λ x → f x) ≡ f
Π-eta f = refl

Σ-eta : {A : Set}{B : A → Set}(p : Σ A B) → 
        (proj₁ p , proj₂ p) ≡ p
Σ-eta p = refl
\end{code}