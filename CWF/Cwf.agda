
open import Level
open import Relation.Binary.PropositionalEquality as PE hiding (refl ; sym ; trans; isEquivalence)

module Cwf (ext : Extensionality zero zero) where

open import Data.Nat
open import Data.Product
open import Data.Rational
open import Function

open import Relation.Binary
open import Relation.Binary.Core public using (_≡_; _≢_)
open import Data.Unit

import HProp1
module x = HProp1 ext
open x

-- Definition of Context

Type = Set₁

-- Context are interpreted as setoids

record Con : Type where
  infix 4 _≈_
  field
    set   : Set
    _≈_   : set → set → HProp
    refl  : {x : set} → < x ≈ x >
    sym   : {x y : set} → < x ≈ y > → < y ≈ x >
    trans : {x y z : set} → < x ≈ y > → < y ≈ z > → < x ≈ z >
  
  _≈'_ : set → set → Set
  a ≈' b = < a ≈ b >
  uip : ∀{a b : set}{p q : a ≈' b} → p ≡ q
  uip {a} {b} = Uni (a ≈ b)
open Con renaming (_≈_ to [_]_≈p_ ; _≈'_ to [_]_≈_ ; set to ∣_∣ ; trans to [_]trans)


-- Context morphism (substitution)

infix 5 _⇉_

record _⇉_ (Γ Δ : Con) : Set where
  field
    fn   : ∣ Γ ∣ → ∣ Δ ∣
    resp : {x y : ∣ Γ ∣} → 
           [ Γ ] x ≈ y → 
           [ Δ ] fn x ≈ fn y

open _⇉_


lemma1 : ∀ {Γ Δ : Con}(f : Γ ⇉ Δ)(x : ∣ Γ ∣) →
         resp f (refl Γ {x}) ≡ refl Δ {fn f x}
lemma1 {Γ} {Δ} f x = uip Δ

lemma2 : {Γ Δ : Con}{x y z : ∣ Γ ∣}(f : Γ ⇉ Δ)
         (p : [ Γ ] x ≈ y)(q : [ Γ ] y ≈ z) → 
         [ Δ ]trans (resp f p) (resp f q) ≡ resp f ([ Γ ]trans p q)
lemma2 {Γ} {Δ} f p q = uip Δ

--verification of categorical laws

-- identity

idCon : (Γ : Con) → Γ ⇉ Γ 
idCon Γ = record { fn = λ x → x; resp = λ x → x }

-- composition

_∘c_ : {Γ Δ Z : Con} → Γ ⇉ Δ → Δ ⇉ Z → Γ ⇉ Z
xy ∘c yz = record { fn = λ x → fn yz (fn xy x); resp = λ x → resp yz (resp xy x) }


------------------------------------
-- Types and Terms

record Ty (Γ : Con) : Type where
  field
    fm     : ∣ Γ ∣ → Con
    substT : {x y : ∣ Γ ∣} → [ Γ ] x ≈ y → ∣ fm x ∣ → ∣ fm y ∣
    subst* : ∀ {x y : ∣ Γ ∣}(p : [ Γ ] x ≈ y){a b : ∣ fm x ∣} → [ fm x ] a ≈ b
             → [ fm y ] substT p a ≈ substT p b
    refl*  : ∀ (x : ∣ Γ ∣)(a : ∣ fm x ∣) → [ fm x ] substT (refl Γ) a ≈ a
    trans* : ∀ {x y z : ∣ Γ ∣}(p : [ Γ ] x ≈ y)(q : [ Γ ] y ≈ z)(a : ∣ fm x ∣)
             → [ fm z ] substT q (substT p a) ≈ substT ([ Γ ]trans p q) a

open Ty

_[_] : ∀ {Γ Δ : Con} → Ty Δ → Γ ⇉ Δ → Ty Γ
Ay [ f ] = record 
          { fm      = λ x → fm Ay (fn f x)
          ; substT = λ {x} {y} p → substT Ay (resp f p)
          ; subst* = λ {x} {y} p → subst* Ay (resp f p)
          ; refl*  = λ x a → subst (λ t → [ fm Ay (fn f x) ] (substT Ay t a) ≈ a) (PE.sym (lemma1 f x)) (refl* Ay (fn f x) a)
          ; trans* = λ {x} {y} {z} p q a → subst (λ t → [ fm Ay (fn f z) ] substT Ay (resp f q) (substT Ay (resp f p) a) ≈ substT Ay t a)  (lemma2 f p q) (trans* Ay (resp f p) (resp f q) a)
          }


-- verification

record Tm {Γ : Con}(A : Ty Γ) : Set where
  field
    tm    : (x : ∣ Γ ∣) → ∣ fm A x ∣
    respt : ∀{x y : ∣ Γ ∣} → (p : [ Γ ] x ≈ y) → [ fm A y ] substT A p (tm x) ≈ tm y

open Tm


_[_]m : ∀ {Γ Δ : Con}{A : Ty Δ} → Tm A → (f : Γ ⇉ Δ) → Tm (A [ f ])
_[_]m t f = record 
          { tm = tm t ∘ fn f
          ; respt = respt t ∘ resp f 
          }


-- verification


----------------------------------------------------
-- Context

● : Con
● = record {
      set = ⊤;
      _≈_ = λ x x' → ⊤';
      refl = tt;
      sym = λ x → tt;
      trans = λ x x' → tt }

-- 1. subst proof irrelevance
-- {Γ : Con}{A : Ty Γ}{}[] p ≈ q → substT A p x ≈ substT A q x
-- can be proved as a separate lemma
-- 2. trans within certain Context can be simplied into reasoning structure
-- uncurry can be replaced by lambda pattern matching

_&_ : (Γ : Con) → Ty Γ → Con
Γ & A = record {
          set = Σ[ x ∶ ∣ Γ ∣ ] ∣ fm A x ∣;
          _≈_ = uncurry (λ x a → uncurry (λ y b → 
                Σ' ([ Γ ] x ≈p y) (λ p → [ fm A y ] substT A p a ≈p b)));
          refl  = λ {x} → (refl Γ) , refl* A (proj₁ x) (proj₂ x);
          sym   = λ {i} {j} → uncurry (λ p q → 
                  (sym Γ p) , 
                  [ fm A (proj₁ i) ]trans ([ fm A (proj₁ i) ]trans (subst* A (sym Γ p) (sym (fm A (proj₁ j)) q)) ([ fm A (proj₁ i) ]trans (trans* A p (sym Γ p) (proj₂ i)) (subst (λ x → [ fm A (proj₁ i) ] substT A x (proj₂ i) ≈ substT A (refl Γ) (proj₂ i)) (Uni ([ Γ ] proj₁ i ≈p proj₁ i)) (refl (fm A (proj₁ i)))))) (refl* A (proj₁ i) (proj₂ i))) ;
          trans = λ {i} {j} {k} → uncurry (λ x a → uncurry (λ y b → [ Γ ]trans x y , [ fm A (proj₁ k) ]trans ([ fm A (proj₁ k) ]trans (sym (fm A (proj₁ k)) (trans* A x y (proj₂ i))) (subst* A y a)) b)) }


-- empty substitution

⍟ : (Δ : Con) → Δ ⇉ ●
⍟ Δ = record 
      { fn = λ _ → tt
      ; resp = λ _ → tt }


-- pairing operation

_,,_ : {Γ Δ : Con}{A : Ty Δ}(f : Γ ⇉ Δ) → (Tm (A [ f ])) → Γ ⇉ (Δ & A)
f ,, t = record 
         { fn = λ x → (fn f x) , (tm t x)
         ; resp = λ p → (resp f p) , respt t p }

-- projections

fst : {Γ Δ : Con}{A : Ty Δ} → Γ ⇉ (Δ & A) → Γ ⇉ Δ
fst f = record 
        { fn = λ x → proj₁ (fn f x)
        ; resp = λ p → proj₁ (resp f p) }


snd : {Γ Δ : Con}{A : Ty Δ} → (f : Γ ⇉ (Δ & A)) → Tm (A [ fst {A = A} f ])
snd f = record 
        { tm = λ x → proj₂ (fn f x)
        ; respt = λ p → proj₂ (resp f p) }


_^_ : {Γ Δ : Con}(f : Γ ⇉ Δ)(A : Ty Δ) → Γ & A [ f ] ⇉ Δ & A
f ^ A = {!f ∘c ? , snd ?!}