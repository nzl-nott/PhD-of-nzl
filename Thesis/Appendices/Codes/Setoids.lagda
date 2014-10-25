\AgdaHide{
\begin{code}

module Setoids where

open import Relation.Binary.Core as Core using (_≡_)

open import Data.Product

open Core public hiding (_≡_; refl; _≢_)


_⇔_ : (A B : Set) → Set
A ⇔ B = (A → B) × (B → A)

\end{code}
}

\begin{code}
record Setoid : Set₁ where
  infix 4 _~_
  field
    Carrier       : Set
    _~_           : Carrier → Carrier → Set
    isEquivalence : IsEquivalence _~_

  open IsEquivalence isEquivalence public
\end{code}
