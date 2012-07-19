{-# OPTIONS --type-in-type #-}

module Cats.Duality where

open import Relation.Binary.PropositionalEquality

open import Cats.Category

Op : Category → Category
Op ℂ = record
  { obj        = obj ℂ
  ; hom        = λ α β → hom ℂ β α
  ; id         = id ℂ
  ; [_⇒_]_∘_   = λ α γ g f → [ γ ⇒ α ] f · g
  ; isCategory = record
    { id₁  = λ α β f     → id₂ (isCategory ℂ) β α f
    ; id₂  = λ α β f     → id₁ (isCategory ℂ) β α f
    ; comp = λ α δ f g h → sym (comp (isCategory ℂ) δ α h g f)
    }
  }
  where
    open Cats.Category.Category
    open Cats.Category.IsCategory

    [_⇒_]_·_ = [_⇒_]_∘_ ℂ

open import Data.Unit

-- postulate
--   irr : ∀ {α : Set} {x y : α} (p₁ p₂ : x ≡ y)
--       → p₁ ≡ p₂

sym-sym : ∀ {α : Set} {x y : α} (p : x ≡ y) → sym (sym p) ≡ p
sym-sym refl = refl

{-
prf : ∀ (ℂ : Category) → Op (Op ℂ) ≡ ℂ
prf (CatC obj hom id [_⇒_]_∘_ (IsCatC id₁ id₂ comp)) = cong (λ x → CatC obj hom id [_⇒_]_∘_ (IsCatC id₁ id₂ x)) {!!}
  where
    open Cats.Category.Category

-}