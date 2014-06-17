{-# OPTIONS --type-in-type #-}

module Cats.Category where

open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Level

record IsCategory
  (obj      : Set)

  (hom      : obj → obj → Set)

  (id       : ∀ α → hom α α)

  ([_⇒_]_∘_ : ∀ α {β} γ
            → hom β γ
            → hom α β
            → hom α γ)
  : Set
  where
    constructor IsCatC
    field
      id₁  : ∀ α β (f : hom α β)
           → [ α ⇒ β ] f ∘ (id α) ≡ f

      id₂  : ∀ α β (f : hom α β)
           → [ α ⇒ β ] (id β) ∘ f ≡ f

      comp : ∀ α {β γ} δ (f : hom α β) (g : hom β γ) (h : hom γ δ)
           → [ α ⇒ δ ] [ β ⇒ δ ] h ∘ g ∘ f ≡ [ α ⇒ δ ] h ∘ ([ α ⇒ γ ] g ∘ f)

record Category : Set where
  constructor CatC
  field
    obj        : Set

    hom        : obj → obj → Set

    id         : ∀ α
               → hom α α

    [_⇒_]_∘_   : ∀ α {β} γ
               → hom β γ
               → hom α β
               → hom α γ

    isCategory : IsCategory obj hom id [_⇒_]_∘_

  open IsCategory public
  
--   Op : Category
--   Op = record { hom = λ a b → hom b a ; [_⇒_]_∘_ = λ α γ g f → [ γ ⇒ α ] f ∘ g }