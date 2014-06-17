{-# OPTIONS --type-in-type #-}

module Cats.Examples.Functor where

open import Cats.Category as Cat
open import Cats.Functor as Func
open import Function
open import Relation.Binary.PropositionalEquality


IdFunctor : ∀ {C} → Functor C C 
IdFunctor = record 
  { mapObj    = id
  ; mapHom    = λ _ _ x → x
  ; isFunctor = record 
    { mapId = λ _ → refl
    ; map∘  = λ _ _ _ _ → refl
    }
  }
