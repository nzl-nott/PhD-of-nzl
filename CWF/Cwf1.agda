module Cwf1 where

open import Data.Nat
open import Data.Product
open import Data.Rational

open import Level

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE hiding (refl ; sym ; trans; isEquivalence)
open import Relation.Binary.Core public using (_≡_; _≢_)
open import Data.Unit

{-
data Prp : Set₁ where
  prf : .Set → Prp
-}

IsProp   : Set → Set
IsProp P = ∀{p q : P} → p ≡ q

-- The proofs of closedness of Π and Σ of Prop

postulate ext : Extensionality zero zero

Πclose : {A : Set}{B : A → Set} →
         (∀ x → IsProp (B x)) → 
         IsProp (∀ x → (B x))
Πclose ispb = ext (λ x → ispb x)



-- Definition of Context

Type = Set₁

record Con : Type where
  infix 4 _≈_
  field
    set   : Set
    _≈_   : set → set → Set
    uip   : ∀ (x y : set) → IsProp (x ≈ y) -- UIP instead of Prop universe
    refl  : Reflexive _≈_
    sym   : Symmetric _≈_
    trans : Transitive _≈_

open Con renaming (_≈_ to [_]_≈_ ; set to ∣_∣)


-- Context morphism

infix 5 _⇉_

record _⇉_ (X Y : Con) : Set where
  field
    fn   : ∣ X ∣ → ∣ Y ∣
    resp : ∀{x y : ∣ X ∣} → [ X ] x ≈ y → [ Y ] fn x ≈ fn y

open _⇉_

lemma1 : ∀ {X Y : Con}(f : X ⇉ Y)(x : ∣ X ∣) → resp f (refl X {x}) ≡ refl Y {fn f x}
lemma1 {X} {Y} f x = uip Y (fn f x) (fn f x)


lemma2 :  {X Y : Con}{x y z : ∣ X ∣}(f : X ⇉ Y)(p : [ X ] x ≈ y)(q : [ X ] y ≈ z) → trans Y (resp f p) (resp f q) ≡ resp f (trans X p q)
lemma2 {X} {Y} {x} {y} {z} f p q = {!!} -- uip Y (fn f x) (fn f z) (resp f (trans X p q)) (trans Y (resp f p) (resp f q))

--verification of categorical laws

-- identity

idCon : (X : Con) → X ⇉ X 
idCon X = record { fn = λ x → x; resp = λ x → x }

-- composition

_∘_ : {X Y Z : Con} → X ⇉ Y → Y ⇉ Z → X ⇉ Z
xy ∘ yz = record { fn = λ x → fn yz (fn xy x); resp = λ x → resp yz (resp xy x) }



-------------------------------------
-- Types and Terms

record Ty (X : Con) : Type where
  field
    fm     : ∣ X ∣ → Con
    substT  : {x y : ∣ X ∣} → [ X ] x ≈ y → ∣ fm x ∣ → ∣ fm y ∣
    subst* : ∀ {x y : ∣ X ∣}(p : [ X ] x ≈ y)(a b : ∣ fm x ∣) → [ fm x ] a ≈ b
             → [ fm y ] substT p a ≈ substT p b
    refl*  : ∀ (x : ∣ X ∣)(a : ∣ fm x ∣) → [ fm x ] substT (refl X) a ≈ a
    trans* : ∀ {x y z : ∣ X ∣}(p : [ X ] x ≈ y)(q : [ X ] y ≈ z)(a : ∣ fm x ∣)
             → [ fm z ] substT q (substT p a) ≈ substT (trans X p q) a

open Ty

_[_] : ∀ {X Y : Con} → Ty Y → X ⇉ Y → Ty X
Ay [ f ] = record 
          { fm      = λ x → fm Ay (fn f x)
          ; substT = λ {x} {y} p → substT Ay (resp f p)
          ; subst* = λ {x} {y} p → subst* Ay (resp f p)
          ; refl*  = λ x a → subst (λ t → [ fm Ay (fn f x) ] (substT Ay t a) ≈ a) (PE.sym (lemma1 f x)) (refl* Ay (fn f x) a)
          ; trans* = {!!} -- λ {x} {y} {z} p q a → subst (λ t → [ fm Ay (fn f z) ] substT Ay (resp f q) (substT Ay (resp f p) a) ≈ (substT Ay t a)) (PE.sym (lemma2 f p q)) (trans* Ay (resp f p) (resp f q) a)
          }


-- verification

record Tm {X : Con}(A : Ty X) : Set where
  field
    tm    : (x : ∣ X ∣) → ∣ fm A x ∣
    respt : ∀{x y : ∣ X ∣} → (p : [ X ] x ≈ y) → [ fm A y ] substT A p (tm x) ≈ tm y

open Tm


_[_]m : ∀ {X Y : Con}{A : Ty Y} → Tm A → (f : X ⇉ Y) → Tm (A [ f ])
_[_]m t f = record 
          { tm = {!!} -- tm t ∘ fn f
          ; respt = {!!} -- respt t ∘ resp f 
          }


-- verification


----------------------------------------------------
-- Context

● : Con
● = record {
      set = ⊤;
      _≈_ = λ _ _ → ⊤;
      uip = λ x y p q → PE.refl;
      refl = tt;
      sym = λ x → tt;
      trans = λ x x' → tt }




_&_ : (X : Con) → Ty X → Con
X & A = record {
          set = Σ[ x ∶ ∣ X ∣ ] ∣ fm A x ∣;
          _≈_ = λ x y → Σ ([ X ] (proj₁ x) ≈ (proj₁ y)) (λ p → [ fm A (proj₁ y) ] (substT A p (proj₂ x)) ≈ (proj₂ y));
          uip  = λ x y p q → {!PE.refl!};
          refl = {!!};
          sym = {!!};
          trans = {!!} }