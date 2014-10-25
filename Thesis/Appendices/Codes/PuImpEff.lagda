
\textbf{Proof :} The propositional univalence (propositional extensionality) implies that a quotient is always exact.

\AgdaHide{
\begin{code}

{-# OPTIONS --type-in-type #-}

open import Setoids
open import Relation.Binary.PropositionalEquality as PE
  hiding ([_])
open import Quotient
open import Data.Product

module PuImpEff
\end{code}
}

Assume we have the propositional univalence (the other direction trivial holds)

\begin{code}
  (PropUni₁ : ∀ {p q : Set} → (p ⇔ q) → p ≡ q)
  {S : Setoid}
  {PQ : pre-Quotient S}
  {Qu : Hof-Quotient PQ}
    where
  open pre-Quotient PQ
  open Hof-Quotient Qu

  coerce : {A B : Set} → A ≡ B → A → B
  coerce refl m = m

  exact : ∀ a a' → [ a ] ≡ [ a' ] → a ~ a'
  exact a a' p = coerce P^-β (~-refl {a})
        where
          P : A → Set
          P x = a ~ x

          isEqClass : ∀ {a b} → a ~ b → P a ⇔ P b
          isEqClass p = (λ q → ~-trans q p) , 
                            (λ q → ~-trans q (~-sym p))

          P-resp : P respects _~_
          P-resp p = PropUni₁ (isEqClass p)

          P^ : Q → Set
          P^ = lift P P-resp

          P^-β : P a ≡ P a'
          P^-β = trans (sym (lift-β _)) 
                 (trans (cong P^ p) (lift-β _))
\end{code}