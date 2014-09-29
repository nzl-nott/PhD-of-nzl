{-# OPTIONS --type-in-type #-}

module Isomorphism where

open import Category as Cat
open import Relation.Binary.PropositionalEquality


record IsIsomorphism
  (C   : Category)
  (α β : Category.obj C)
  (f   : Category.hom C α β)
  (f⁻¹ : Category.hom C β α)
  : Set
  where
    open Category C
    open IsCategory isCategory
    field
      prop₁ : [ α ⇒ α ] f⁻¹ ∘ f   ≡ id α
      prop₂ : [ β ⇒ β ] f   ∘ f⁻¹ ≡ id β

record Isomorphism
  (C   : Category)
  (α β : Category.obj C)
  : Set
  where
    open Category C
    field
      f             : hom α β
      f⁻¹           : hom β α
      isIsomorphism : IsIsomorphism C α β f f⁻¹
