module MyProp where

open import Relation.Binary.PropositionalEquality

open import Data.Product

record HProp : Set₁ where
  constructor hProp
  field
    Prf : Set
    Unique : (p q : Prf) → p ≡ q

open HProp

record SquashSet (A : Set) : Set where
   constructor squashSet
   field
     .proof : A

pirr : {P : Set}(p q : SquashSet P) → p ≡ q
pirr (squashSet p) (squashSet p') = refl

Squash : Set → HProp
Squash A = hProp (SquashSet A) pirr

