module Cwf_hprop1 where

open import Data.Nat
open import Data.Product hiding (Σ)
open import Relation.Binary.PropositionalEquality as PE hiding (refl ; sym ; trans; isEquivalence; [_])
open import Relation.Binary.Core public using (_≡_; _≢_)
open import Function
open import Data.Unit
open import HProp

Type = Set₁


record Con : Type where
  infix 4 _≈_
  field
    set    : Set
    _≈_    : set → set → HProp
    refl   : ∀{x : set} → ⟦ x ≈ x ⟧
    sym    : ∀{x y : set} → ⟦ x ≈ y ⟧ → ⟦ y ≈ x ⟧
    trans  : ∀{x y z : set} → ⟦ x ≈ y ⟧ → ⟦ y ≈ z ⟧ → ⟦ x ≈ z ⟧

open Con renaming (_≈_ to [_]_≈_ ; set to ∣_∣)

-- morphisms

infix 5 _⇉_

record _⇉_ (X Y : Con) : Set where
  field
    fn   : ∣ X ∣ → ∣ Y ∣
    resp : ∀{x y : ∣ X ∣} → ⟦ [ X ] x ≈ y ⟧ → ⟦ [ Y ] fn x ≈ fn y ⟧

open _⇉_

-----------------------
-- Con forms a category

-- identity

idCon : {X : Con} → X ⇉ X 
idCon = record { fn = id ; resp = id }

-- composition


_∘'_ : {X Y Z : Con} → X ⇉ Y → Y ⇉ Z → X ⇉ Z
_∘'_ xy yz = record { fn = fn yz ∘ fn xy ; resp = resp yz ∘ resp xy }


-------------------------------------
-- Types and Terms

record Ty (X : Con) : Type where
  field
    fm     : ∣ X ∣ → Con
    substT  : {x y : ∣ X ∣} → ⟦ [ X ] x ≈ y ⟧ → ∣ fm x ∣ → ∣ fm y ∣
    subst* : ∀ {x y : ∣ X ∣}(p : ⟦ [ X ] x ≈ y ⟧)(a b : ∣ fm x ∣) → ⟦ [ fm x ] a ≈ b ⟧
             → ⟦ [ fm y ] substT p a ≈ substT p b ⟧
    refl*  : ∀ (x : ∣ X ∣)(a : ∣ fm x ∣) → ⟦ [ fm x ] substT (refl X) a ≈ a ⟧
    trans* : ∀ {x y z : ∣ X ∣}(p : ⟦ [ X ] x ≈ y ⟧)(q : ⟦ [ X ] y ≈ z ⟧)(a : ∣ fm x ∣)
             → ⟦ [ fm z ] substT q (substT p a) ≈ substT (trans X p q) a ⟧

open Ty


lemma1 : ∀ {X Y : Con}(f : X ⇉ Y)(x : ∣ X ∣) → refl Y {fn f x} ≡ resp f (refl X)
lemma1 f x = PE.refl


lemma2 :  {X Y : Con}{x y z : ∣ X ∣}(f : X ⇉ Y)(p : ⟦ [ X ] x ≈ y ⟧)(q : ⟦ [ X ] y ≈ z ⟧) → trans Y (resp f p) (resp f q) ≡ resp f (trans X p q)
lemma2 f p q = PE.refl

--verification of categorical laws



_[_] : ∀ {X Y : Con} → Ty(Y) → X ⇉ Y → Ty(X)
Ay [ f ] = record 
          { fm     = λ x → fm Ay (fn f x)
          ; substT = λ {x} {y} p → substT Ay (resp f p)
          ; subst* = λ {x} {y} p → subst* Ay (resp f p)
          ; refl*  = λ x a → subst (λ t → ⟦ [ fm Ay (fn f x) ] (substT Ay t a) ≈ a ⟧) (lemma1 f x) (refl* Ay (fn f x) a)
          ; trans* = λ {x} {y} {z} p q a → subst (λ t → ⟦ [ fm Ay (fn f z) ] substT Ay (resp f q) (substT Ay (resp f p) a) ≈ (substT Ay t a) ⟧) (lemma2 f p q) (trans* Ay (resp f p) (resp f q) a)
          }


-- verification

record Tm {X : Con}(A : Ty X) : Set where
  field
    tm    : (x : ∣ X ∣) → ∣ fm A x ∣
    respt : ∀{x y : ∣ X ∣} → (p : ⟦ [ X ] x ≈ y ⟧) → ⟦ [ fm A y ] substT A p (tm x) ≈ tm y ⟧

open Tm

_[_]m : ∀ {X Y : Con}{A : Ty Y} → Tm A → (f : X ⇉ Y) → Tm (A [ f ])
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
      _≈_ = λ _ _ → ⊤';
      refl = sp tt;
      sym = λ x → x;
      trans = λ x x' → x }


_&_ : (X : Con) → Ty X → Con
X & A = record {
          set = Σ' ∣ X ∣ (λ x → ∣ fm A x ∣);
          _≈_ = λ x y → hProp (Σ' (⟦ [ X ] fst x ≈ fst y ⟧) (λ p → ⟦ [ fm A (fst y) ] substT A p (snd x) ≈ snd y ⟧)) (λ p q → PE.refl) ;
          refl  = λ {x} → sp (refl X , refl* A (fst x) (snd x));
          sym   = λ {x} {y} → λ eq → {!!};
          trans = {!!} }
-- λ x y → Σ-p ([ X ] fst x ≈ fst y) (λ p → ([ fm A (fst y) ] substT A (sp p) (snd x) ≈ snd y))