{-# OPTIONS --type-in-type #-}

module Cats.Functor where

open import Relation.Binary.PropositionalEquality
open import Cats.Category as Cat

open Category

record IsFunctor
  (C₁ C₂  : Category)

  (mapObj : Category.obj C₁
          → Category.obj C₂)

  (mapHom : ∀ α β 
          → Category.hom C₁         α          β
          → Category.hom C₂ (mapObj α) (mapObj β))
  : Set
  where
    open Category

    [_⇒_]_∘₁_ : ∀ α {β} γ
              → hom C₁ β γ
              → hom C₁ α β
              → hom C₁ α γ
    [_⇒_]_∘₁_ = [_⇒_]_∘_ C₁

    [_⇒_]_∘₂_ : ∀ α {β} γ
              → hom C₂ β γ
              → hom C₂ α β
              → hom C₂ α γ
    [_⇒_]_∘₂_ = [_⇒_]_∘_ C₂

    field
      mapId : ∀ α
            → mapHom α α (id C₁ α) ≡ id C₂ (mapObj α)

      map∘  : ∀ α {β} γ (f : hom C₁ α β) (g : hom C₁ β γ)
            → mapHom α γ ([ α ⇒ γ ] g ∘₁ f) ≡ [ mapObj α ⇒ mapObj γ ] (mapHom β γ g) ∘₂ (mapHom α β f)

record Functor (C₁ C₂ : Category) : Set where
  open Category
  field
    mapObj    : obj C₁
              → obj C₂

    mapHom    : ∀ α β
              → hom C₁         α          β
              → hom C₂ (mapObj α) (mapObj β)

    isFunctor : IsFunctor C₁ C₂ mapObj mapHom

  
  open IsFunctor public
  FunctorObj : Set
  FunctorObj = obj C₁ → obj C₂
  
  FunctorHom : Set
  FunctorHom = ∀ α β
              → hom C₁         α          β
              → hom C₂ (mapObj α) (mapObj β)
  
open Functor
