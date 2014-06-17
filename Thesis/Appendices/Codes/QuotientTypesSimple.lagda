\begin{code}


module QuotientTypesSimple where

open import Data.Product
import Level
open import Relation.Binary.PropositionalEquality hiding (refl; [_])

import Relation.Binary as RB

Setoid = RB.Setoid Level.zero Level.zero
\end{code}

\begin{code}

record Quotient (S : Setoid) : Set₁ where
  open RB.Setoid S renaming (Carrier to A ; _≈_ to _~_)
  field
    Q : Set
    [_] : A → Q
    [_]⁼ : {a a' : A} → a ~ a' → [ a ] ≡ [ a' ]
    qelim : (B : Q → Set)(f : (x : A) → B [ x ])
           → (∀ a a' → (p : a ~ a') → 
             subst (λ x → B x) [ p ]⁼ (f a) ≡ f a')
           → (x : Q) → B x
    qelim-β : ∀ B f f⁼ x → qelim B f f⁼ [ x ] ≡ f x


postulate QType : (s : Setoid) → Quotient s

module UA-EF (UA : )


{-
{-
  qind 　: (P : Q → Prp) 
         → ∣ ∀'[ a ∶ A ] P [ a ] ∣
         → ∣ ∀'[ x ∶ Q ] P x ∣
  qind = {!!}
-}

module Lemmas (A : Set)(_∼_ : bRel A)(equiv : ∣ Equiv _∼_ ∣) where

  quotients = QType (A , _∼_ , equiv)
  open Quotient quotients


  _∼^_ : Q → Q → Prp
  _∼^_ q q' = {!!}
-}
\end{code}
