{-# OPTIONS --type-in-type #-}

module Examples.Isomorphism where

open import Isomorphism as Iso
open import Product as Prod
open import Relation.Binary.PropositionalEquality
open import Examples.Category
open import Data.Product


comm : ∀ {α β : Set} → Isomorphism SET (α × β) (β × α)
comm = record
  { f             = λ x → proj₂ x , proj₁ x
  ; f⁻¹           = λ x → proj₂ x , proj₁ x
  ; isIsomorphism = record
    { prop₁ = {!!}
    ; prop₂ = {!!}
    }
  }