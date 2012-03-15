module Cwf_hprop where

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
    refl   : < Π (λ x → x ≈ x) >
    sym    : < Π (λ x → Π (λ y → x ≈ y  ⇛ y ≈ x)) >
    trans  : ?

open Con

infix 5 _⇉_

record _⇉_ (X Y : Con) : Set where
  field
    f    : set X → set Y
    resp : ∀ {x y : set X} → < (_≈_ X) x y ⇛ (_≈_ Y) (f x) (f y) >

open _⇉_

lemma1 : ∀ {X Y : Con}(fxy : X ⇉ Y)(x : set X) → app (resp fxy) (app (refl X) x) ≡ refl Y {f fxy x}
lemma1 {X} {Y} fxy x = ? -- isProp Y (f fxy x) (f fxy x) (resp fxy (refl X {x})) (refl Y {f fxy x})


lemma2 :  {X Y : Con}{x y z : set X}(fxy : X ⇉ Y)(p : _≈_ X x y)(q : _≈_ X y z) → resp fxy (trans X p q) ≡ trans Y (resp fxy p) (resp fxy q) 
lemma2 {X} {Y} {x} {y} {z} fxy p q = ? --  isProp Y (f fxy x) (f fxy z) (resp fxy (trans X p q)) (trans Y (resp fxy p) (resp fxy q))

--verification of categorical laws

-- identity

idCon : (X : Con) → X ⇉ X 
idCon X = record { f = λ x → x; resp = λ x → x }

-- composition

_∘_ : {X Y Z : Con} → X ⇉ Y → Y ⇉ Z → X ⇉ Z
xy ∘ yz = record { f = λ x → f yz (f xy x); resp = λ x → resp yz (resp xy x) }



-------------------------------------
-- Types and Terms

record Ty (X : Con) : Type where -- Set₁ should be Con, but failed here
  field
    A      : set X → Con
    Asubst : {x y : set X} → ((_≈_ X) x y) → set (A x) → set (A y)
    subPre : ∀ {x y : set X}(p : (_≈_ X) x y)(a b : set (A x)) → ((_≈_ (A x)) a b)
             → (_≈_ (A y)) (Asubst p a) (Asubst p b)
    Arefl  : ∀ (x : set X)(a : set (A x)) → (_≈_ (A x)) (Asubst (refl X) a) a
    Atrans : ∀ {x y z : set X}(p : (_≈_) X x y)(q : (_≈_) X y z)(a : set (A x))
             → (_≈_ (A z)) (Asubst q (Asubst p a)) (Asubst (trans X p q) a)

open Ty

_[_] : ∀ {X Y : Con} → Ty(Y) → X ⇉ Y → Ty(X)
Ay [ fxy ] = record 
          { A      = λ x → A Ay (f fxy x)
          ; Asubst = λ {x} {y} p → Asubst Ay (resp fxy p)
          ; subPre = λ {x} {y} p → subPre Ay (resp fxy p)
          ; Arefl  = λ x a → subst (λ t → (_≈_ (A Ay (f fxy x))) (Asubst Ay t a) a) (PE.sym (lemma1 fxy x)) (Arefl Ay (f fxy x) a)
          ; Atrans = λ {x} {y} {z} p q a → subst (λ t → (A Ay (f fxy z) ≈ Asubst Ay (resp fxy q) (Asubst Ay (resp fxy p) a)) 
                    (Asubst Ay t a)) (PE.sym (lemma2 fxy p q)) (Atrans Ay (resp fxy p) (resp fxy q) a)
          }

