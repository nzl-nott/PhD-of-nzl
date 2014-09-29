{-# OPTIONS --type-in-type #-}

module MonoidHomomorphism where

open import Relation.Binary.PropositionalEquality
open import Algebra

{-
record IsMonoidHomomorphism 
  (A B : Monoid)
  (map : Monoid.Carrier A → Monoid.Carrier B)
  : Set
  where
    open Monoid
    field
      ⇒-ε : map (ε A) ≡ ε B
      ⇒-∙ : ∀ {α β} → map ((A ∙ α) β) ≡ (B ∙ (map α)) (map β)

record MonoidHomomorphism 
  (A B : Monoid)
  : Set
  where
    field
      map : Monoid.Carrier A → Monoid.Carrier B
      isMonoidHomomorphism : IsMonoidHomomorphism A B map
-}
