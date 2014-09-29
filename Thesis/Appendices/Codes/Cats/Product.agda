{-# OPTIONS --type-in-type #-}

module Product where

open import Category as Cat
open import Data.Product
open import Relation.Binary.PropositionalEquality

record IsProduct
  (C       : Category)
  (α β α×β : Category.obj C)
  (π₁      : Category.hom C α×β α)
  (π₂      : Category.hom C α×β β)
  : Set
  where
    open Category C
    field
      ump : ∀ {χ : obj} (f : hom χ α) (g : hom χ β)
          → ∃! _≡_ (λ h → f ≡ [ χ ⇒ α ] π₁ ∘ h × g ≡ [ χ ⇒ β ] π₂ ∘ h)

    ⟨_,_⟩ : ∀ {χ : obj} → hom χ α → hom χ β → hom χ α×β
    ⟨ f , g ⟩ = proj₁ (ump f g)

record Product (C : Category) (α β : Category.obj C) : Set where
  open Category C
  field
    α×β       : obj
    π₁        : hom α×β α
    π₂        : hom α×β β
    isProduct : IsProduct C α β α×β π₁ π₂
