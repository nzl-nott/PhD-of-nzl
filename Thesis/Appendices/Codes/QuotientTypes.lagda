\begin{code}

open import Level
open import Relation.Binary.PropositionalEquality hiding (refl; [_])

module QuotientTypes  (ext : Extensionality zero zero) where

open import Data.Product

open import Prp ext
\end{code}

1. Equivalence relation

a binary relation is

\begin{code}
bRel : (A : Set) → Set₁
bRel A = A → A → Prp

Refl : {A : Set} → bRel A → Prp
Refl {A} _~_ = ∀'[ a ∶ A ] (a ~ a)

Symm : {A : Set} → bRel A → Prp
Symm {A} _~_ = ∀'[ a ∶ A ] ∀'[ b ∶ A ] a ~ b ⇒ b ~ a


Tran : {A : Set} → bRel A → Prp
Tran {A} _~_ = ∀'[ a ∶ A ] ∀'[ b ∶ A ] ∀'[ c ∶ A ] a ~ b ⇒ b ~ c ⇒ a ~ c


Equiv : {A : Set}(_∼_ : bRel A) → Prp
Equiv {A} _∼_ = Refl _∼_ ∧ Symm _∼_ ∧ Tran _∼_

\end{code}




\begin{code}
Setoid : Set₁
Setoid = Σ[ A ∶ Set ] Σ[ _∼_ ∶ bRel A ] ∣ Equiv _∼_ ∣
\end{code}




\begin{code}
record Quotient (A : Set)(_∼_ : bRel A)(equiv : ∣ Equiv _∼_ ∣) : Set₁ where
  field
    Q : Set
    [_] : A → Q
    [_]⁼ : {a a' : A} → ∣ a ∼ a' ∣ → [ a ] ≡ [ a' ]
    qelim : (B : Q → Set)(f : (x : A) → B [ x ])
           → (∀ a a' → (p : ∣ a ∼ a' ∣) → subst (λ x → B x) [ p ]⁼ (f a) ≡ f a')
           → (x : Q) → B x
    qelim-β : ∀ B f f⁼ x → qelim B f f⁼ [ x ] ≡ f x

  
  qind 　: (P : Q → Prp) 
         → ∣ ∀'[ a ∶ A ] P [ a ] ∣
         → ∣ ∀'[ x ∶ Q ] P x ∣
  qind = {!!}

postulate QType : (s : Setoid) → Quotient (proj₁ s) (proj₁ (proj₂ s)) (proj₂ (proj₂ s))


module Lemmas (A : Set)(_∼_ : bRel A)(equiv : ∣ Equiv _∼_ ∣) where

  quotients = QType (A , _∼_ , equiv)
  open Quotient quotients


  _∼^_ : Q → Q → Prp
  _∼^_ q q' = {!!}

\end{code}
