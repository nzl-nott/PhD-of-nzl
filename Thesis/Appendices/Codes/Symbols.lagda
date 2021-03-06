\begin{code}

module Symbols where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality


infixr 41  _⋆_
infixl 40 _>≡<_

\end{code}
(from Thomas) Some notation to shorten simple proofs or make them more human readable without using heavy  equational reasoning (begin ... )
\begin{code}

⟨_⟩ : ∀ {A : Set} → Symmetric (_≡_ {A = A})
⟨_⟩ = sym

_>≡<_ : ∀ {A : Set} → Transitive (_≡_ {A = A})
_>≡<_ = trans

_⋆_ : ∀ {A B : Set} (f : A → B)
        {x y} → x ≡ y → f x ≡ f y
_⋆_ = cong

\end{code}