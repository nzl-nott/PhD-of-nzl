module Cwf where

open import Data.Nat
open import Data.Product
open import Data.Rational
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE hiding (refl ; sym ; trans; isEquivalence)
open import Relation.Binary.Core public using (_≡_; _≢_)
open import Data.Unit

{-
data Prp : Set₁ where
  prf : .Set → Prp
-}
Type = Set₁


IsProp   : ∀ (P : Set) → Set
IsProp P = (p q : P) → p ≡ q

record Con : Type where
  infix 4 _≈_
  field
    set    : Set
    _≈_    : set → set → Set
    isProp : ∀ (x y : set) → IsProp (x ≈ y) -- UIP instead of Prop universe
    refl   : Reflexive _≈_
    sym    : Symmetric _≈_
    trans  : Transitive _≈_

open Con

pi_close : {A : Set}{B : A → Set} → (∀(x : A) → IsProp (B x)) → IsProp ((x : A) → (B x))
pi_close ispb a b = {!!}


sig_close : {A : Set}{B : A → Set} → IsProp A → (∀(x : A) → IsProp (B x)) → IsProp (Σ[ x ∶ A ] (B x))
sig_close ispa ispb (a1 , a2) (b1 , b2) with ispa a1 b1
sig_close ispa ispb (.b1 , a2) (b1 , b2) | PE.refl with ispb b1 a2 b2
sig_close ispa ispb (.b1 , .b2) (b1 , b2) | PE.refl | PE.refl = PE.refl 


infix 5 _⇉_

record _⇉_ (X Y : Con) : Set where
  field
    f    : set X → set Y
    resp : ∀ {x y : set X} → ((_≈_ X) x y) → (_≈_ Y) (f x) (f y)

open _⇉_

lemma1 : ∀ {X Y : Con}(fxy : X ⇉ Y)(x : set X) → resp fxy (refl X {x}) ≡ refl Y {f fxy x}
lemma1 {X} {Y} fxy x = isProp Y (f fxy x) (f fxy x) (resp fxy (refl X {x})) (refl Y {f fxy x})


lemma2 :  {X Y : Con}{x y z : set X}(fxy : X ⇉ Y)(p : _≈_ X x y)(q : _≈_ X y z) → resp fxy (trans X p q) ≡ trans Y (resp fxy p) (resp fxy q) 
lemma2 {X} {Y} {x} {y} {z} fxy p q = isProp Y (f fxy x) (f fxy z) (resp fxy (trans X p q)) (trans Y (resp fxy p) (resp fxy q))

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

_[_]y : ∀ {X Y : Con} → Ty(Y) → X ⇉ Y → Ty(X)
Ay [ fxy ]y = record 
          { A      = λ x → A Ay (f fxy x)
          ; Asubst = λ {x} {y} p → Asubst Ay (resp fxy p)
          ; subPre = λ {x} {y} p → subPre Ay (resp fxy p)
          ; Arefl  = λ x a → subst (λ t → (_≈_ (A Ay (f fxy x))) (Asubst Ay t a) a) (PE.sym (lemma1 fxy x)) (Arefl Ay (f fxy x) a)
          ; Atrans = λ {x} {y} {z} p q a → subst (λ t → (A Ay (f fxy z) ≈ Asubst Ay (resp fxy q) (Asubst Ay (resp fxy p) a)) 
                    (Asubst Ay t a)) (PE.sym (lemma2 fxy p q)) (Atrans Ay (resp fxy p) (resp fxy q) a)
          }


-- verification

record Tm (X : Con)(ty : Ty X) : Set where
  field
    t     : (x : set X) → set (A ty x)
    tresp : ∀ {x y : set X} → (p : (_≈_ X x y)) → (_≈_ (A ty y)) (Asubst ty p (t x)) (t y)

open Tm

_[_]m : ∀ {X Y : Con}{ty : Ty Y} → Tm Y ty → (fxy : X ⇉ Y) → Tm X (ty [ fxy ]y)
_[_]m {X} {Y} {ty} tm fxy
             = record 
             { t = λ x → t tm (f fxy x)
             ; tresp = λ p → tresp tm (resp fxy p) 
             }

-- verification


----------------------------------------------------
-- Context

● : Con
● = record {
      set = ⊤;
      _≈_ = λ _ _ → ⊤;
      isProp = λ x y p q → PE.refl;
      refl = tt;
      sym = λ x → tt;
      trans = λ x x' → tt }

_&_ : (X : Con) → Ty X → Con
X & ty = record {
          set = Σ[ x ∶ set X ] set (A ty x);
          _≈_ = λ x y → Σ ((X ≈ proj₁ x) (proj₁ y)) (λ p → (A ty (proj₁ y) ≈ (Asubst ty p (proj₂ x))) (proj₂ y));
          isProp = λ x y p q → {!PE.refl!};
          refl = {!!};
          sym = {!!};
          trans = {!!} }