{-# OPTIONS --type-in-type #-}

module Cats.Examples.Category where

open import Cats.Category
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Unit
open import Data.Product
  hiding (map)
open import Algebra


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

-- FIXME: Use stdlib for commutativeSemiring 

n+0≡n : {n : ℕ} → n + 0 ≡ n
n+0≡n {zero}  = refl
n+0≡n {suc n} rewrite n+0≡n {n} = refl

+-assoc : ∀ {n m o} → ((n + m) + o) ≡ (n + (m + o))
+-assoc {zero} = refl
+-assoc {suc n} = cong suc (+-assoc {n})

ℕ-Monoid : Category
ℕ-Monoid = record 
  { obj        = ⊤
  ; hom        = λ _ _ → ℕ
  ; id         = λ _ → 0
  ; [_⇒_]_∘_   = λ _ _ n m → n + m
  ; isCategory = record 
    { id₁  = λ _ _ _ → n+0≡n
    ; id₂  = λ _ _ _ → refl
    ; comp = λ _ _ _ _ h → +-assoc {h}
    }
  }


open import MonoidHomomorphism 
open import Function
open ≡-Reasoning

{-
Monoid-Cat : Category
Monoid-Cat = record 
  { obj        = Monoid
  ; hom        = λ α β → MonoidHomomorphism α β 
  ; id         = λ α → record 
    { map = λ α → α
    ; isMonoidHomomorphism = record 
      { ⇒-ε = refl
      ; ⇒-∙ = refl
      }
    }
  ; [_⇒_]_∘_   = λ α {β} γ n m → record 
    { map = map n ∘ map m
    ; isMonoidHomomorphism = record
      { ⇒-ε =
        begin
          map n (map m (ε α))
            ≡⟨ cong (map n) (⇒-ε (isMonoidHomomorphism m)) ⟩
          map n (ε β)
            ≡⟨ ⇒-ε (isMonoidHomomorphism n) ⟩
          ε γ
        ∎
      ; ⇒-∙ = λ {φ ψ} →
        begin
          map n (map m (_∙_ α φ ψ))
            ≡⟨ cong (map n) (⇒-∙ (record 
              { ⇒-ε = refl
              ; ⇒-∙ = refl
              })) ⟩
          map n (_∙_ β (map m φ) (map m ψ)) ≡⟨ ⇒-∙ (record
            { ⇒-ε = refl
            ; ⇒-∙ = refl
            }) ⟩
          _∙_ γ (map n (map m φ)) (map n (map m ψ))
        ∎
      }
    }
  ; isCategory = record 
    { id₁ = λ α β f → {!refl!}
    ; id₂  = λ _ _ _ → {!!}
    ; comp = λ _ _ _ _ _ → {!!}
    }
  }
  where
    open Monoid hiding (refl; trans)
    open MonoidHomomorphism.MonoidHomomorphism
    open IsMonoidHomomorphism

    trans-refl-trans-p-refl≡p : {A : Set}{a a' : A}{p : a ≡ a'} → trans refl (trans p refl) ≡ p
    trans-refl-trans-p-refl≡p {p = refl} = refl

    trans-refl-trans-p-refl≡p' : {α β : Monoid}{f : MonoidHomomorphism α β} →
      trans refl (trans (⇒-ε (isMonoidHomomorphism f)) refl) ≡ ⇒-ε (isMonoidHomomorphism f)
    trans-refl-trans-p-refl≡p' {f = f} rewrite trans-refl-trans-p-refl≡p {p = (⇒-ε (isMonoidHomomorphism f))} = refl
-}
