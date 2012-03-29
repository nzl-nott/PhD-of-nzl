module Cwf_hprop1 where

open import Data.Nat
open import Data.Product
open import Data.Rational
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE hiding (refl ; sym ; trans; isEquivalence)
open import Relation.Binary.Core public using (_≡_; _≢_)


open import HProp

Type = Set₁


record Con : Type where
  infix 4 _≈_
  field
    set    : Set
    _≈_    : set → set → HProp
    refl   : ∀{x : set} → ⟦ x ≈ x ⟧
    sym    : ∀{x y : set} → ⟦ x ≈ y ⟧ →  ⟦ y ≈ x ⟧
    trans  : ∀{x y z : set} → ⟦ x ≈ y ⟧ → ⟦ y ≈ z ⟧ → ⟦ x ≈ z ⟧

open Con renaming (_≈_ to [_]_≈_)

-- morphisms

infix 5 _⇉_

record _⇉_ (X Y : Con) : Set where
  field
    f    : set X → set Y
    resp : ∀{x y : set X} → ⟦ [ X ] x ≈ y ⟧ → ⟦ [ Y ] (f x) ≈ (f y) ⟧

open _⇉_

-----------------------
-- Con forms a category

-- identity

idCon : (X : Con) → X ⇉ X 
idCon X = record { f = λ x → x; resp = λ x' → x' }

-- composition


_∘_ : {X Y Z : Con} → X ⇉ Y → Y ⇉ Z → X ⇉ Z
_∘_ {X} {Y} {Z} xy yz =  record { f = λ x → f yz (f xy x); resp = λ eq → resp yz (resp xy eq) }


-------------------------------------
-- Types and Terms

record Ty (X : Con) : Type where -- Set₁ should be Con, but failed here
  field
    A      : set X → Con
    Asubst : {x y : set X} → ⟦ [ X ] x ≈ y ⟧ → set (A x) → set (A y)
    subPre : ∀ {x y : set X}(p : ⟦ [ X ] x ≈ y ⟧)(a b : set (A x)) → ⟦ [ A x ] a ≈ b ⟧
             → ⟦ [ A y ] (Asubst p a) ≈ (Asubst p b) ⟧
    Arefl  : ∀ (x : set X)(a : set (A x)) → ⟦ [ A x ] (Asubst (refl X) a) ≈ a ⟧
    Atrans : ∀ {x y z : set X}(p : ⟦ [ X ] x ≈ y  ⟧)(q : ⟦ [ X ] y ≈ z  ⟧)(a : set (A x))
             → ⟦ [ A z ] Asubst q (Asubst p a) ≈ Asubst (trans X p q) a ⟧

open Ty


lemma1 : ∀ {X Y : Con}(xy : X ⇉ Y)(x : set X) → refl Y {f xy x} ≡ resp xy (refl X)
lemma1 {X} {Y} fxy x = PE.refl


lemma2 :  {X Y : Con}{x y z : set X}(fxy : X ⇉ Y)(p : ⟦ [ X ] x ≈ y ⟧)(q : ⟦ [ X ] y ≈ z ⟧) → trans Y (resp fxy p) (resp fxy q) ≡ resp fxy (trans X p q)
lemma2 {X} {Y} {x} {y} {z} fxy p q = PE.refl

--verification of categorical laws



_[_] : ∀ {X Y : Con} → Ty(Y) → X ⇉ Y → Ty(X)
Ay [ fxy ] = record 
          { A      = λ x → A Ay (f fxy x)
          ; Asubst = λ {x} {y} p → Asubst Ay (resp fxy p)
          ; subPre = λ {x} {y} p → subPre Ay (resp fxy p)
          ; Arefl  = λ x a → subst (λ t → ⟦ [ A Ay (f fxy x) ] (Asubst Ay t a) ≈ a ⟧) (lemma1 fxy x) (Arefl Ay (f fxy x) a)
          ; Atrans = λ {x} {y} {z} p q a → subst (λ t → ⟦ [ A Ay (f fxy z) ] Asubst Ay (resp fxy q) (Asubst Ay (resp fxy p) a) ≈ (Asubst Ay t a) ⟧) (lemma2 fxy p q) (Atrans Ay (resp fxy p) (resp fxy q) a)
          }


