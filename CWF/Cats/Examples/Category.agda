{-# OPTIONS --type-in-type #-}

module Cats.Examples.Category where

open import Cats.Category
open import Cats.Functor
open import Cats.Examples.Functor
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Unit
open import Data.Product
  hiding (map)
open import Algebra

open Category
open Functor


SET : Category
SET = record
  { obj        = Set
  ; hom        = λ α β → α → β
  ; id         = λ _ x → x 
  ; [_⇒_]_∘_   = λ _ _ g f x → g (f x)
  ; isCategory = record
    { id₁  = λ _ _ _ → refl
    ; id₂  = λ _ _ _ → refl
    ; comp = λ _ _ _ _ _ → refl
    }
  }


-- modified by Li Nuo

-- just axiomatize the propositional equality between Functors

postulate extFunctor : {C D : Category}{F G : Functor C D} → 
             (eq1 : ∀ x → mapObj F x ≡ mapObj G x) → 
             (eq2 : ∀ a b c → subst (λ x → hom D x (mapObj G b)) (eq1 a) (subst (λ x → hom D (mapObj F a) x) (eq1 b) (mapHom F a b c)) ≡ mapHom G a b c) →
             F ≡ G

CAT : Category
CAT = record
  { obj        = Category
  ; hom        = λ α β → Functor α β
  ; id         = λ _ → IdFunctor
  ; [_⇒_]_∘_   = λ _ _ g f → 
                  record 
                  { mapObj = (mapObj g) ∘ (mapObj f); mapHom = λ _ _ → (mapHom g _ _) ∘ (mapHom f _ _)
                  ; isFunctor = record { mapId = λ α → trans (cong (λ x → mapHom g (mapObj f α) (mapObj f α) x) (mapId (isFunctor f) _)) (mapId (isFunctor g) _)
                  ; map∘ = λ α γ f' g' → trans (cong (λ x → mapHom g (mapObj f α) (mapObj f γ) x) (map∘ (isFunctor f) _ _ _ _)) (map∘ (isFunctor g) _ _ _ _) } }
  ; isCategory = record
    { id₁  = λ _ _ _ → extFunctor (λ x → refl) (λ a' b' c → refl)
    ; id₂  = λ _ _ _ → extFunctor (λ x → refl) (λ a' b' c → refl)
    ; comp = λ _ _ _ _ _ → extFunctor (λ x → refl) (λ a' b' c → refl)
    }
  }