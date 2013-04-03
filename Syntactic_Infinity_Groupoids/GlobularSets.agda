module GlobularSets where

open import Data.Product
open import Coinduction
open import Relation.Binary.PropositionalEquality
open import DependentEquality

record Glob : Set₁ where
  constructor _∣∣_
  field
    ∣_∣   : Set
    homo : ∣_∣ →  ∣_∣  → ∞ Glob
open Glob public



{-
lemma : (A B : Glob)(p : ∣ A ∣ ≡ ∣ B ∣) → (u v : ∣ A ∣) → (u' v' : ∣ B ∣) → (dEq {B = λ a → a} p u u') → (dEq {B = λ a → a} p v v') → ∣ ♭ (homo A u v) ∣ ≡ ∣ ♭ (homo B u' v') ∣
lemma A B p u v u' v' q r = {!p!}


lemma' : (A B : Set)(p : A ≡ B)(hA : A → A → ∞ Glob)(hB : B → B → ∞ Glob)(ph : dEq p hA hB) → (u v : A) → (u' v' : B) → (dEq {B = λ a → a} p u u') → (dEq {B = λ a → a} p v v') → ∣ ♭ (hA u v) ∣ ≡ ∣ ♭ (hB u' v') ∣
lemma' .B B refl .hB hB (drefl .hB) .u' .v' u' v' (drefl .u') (drefl .v') = refl
-}

EqGlob : (A B : Glob) → (A ≡ B) → Σ (∣ A ∣ ≡ ∣ B ∣) (λ p → dEq {B = λ a → a → a → ∞ Glob} p (homo A) (homo B))
EqGlob .B B refl = refl , drefl _

-- universe definition

module UniverseGS (U : Set)(El : U → Set) where

  record uGlob : Set where
    field
      ∣_∣u   : U
      uhomo : El ∣_∣u → El ∣_∣u → ∞ uGlob
  open uGlob


{-
  Π : (A : uGlob)(B : A → uGlob) → uGlob
  Π A B = 
    record 
    { ∣_∣u = {!El ∣ A ∣u !}
    ; uhomo = {!!} 
    }
-}
-- Globular Sets indexed by Types

Π : (A : Set)(B : A → Glob) → Glob
Π A B = 
  record 
  { ∣_∣ = (a : A) → ∣ B a ∣
  ; homo = λ f g → ♯ Π A (λ x → ♭ (homo (B x) (f x) (g x)))
  }

-- Globular Sets indexed by Globular Sets

-- looks good but we may require it covertible to some Glob
record _⇒Glob (A : Glob) : Set₁ where
  field
    ∣_∣f   : ∣ A ∣ → Set
    homof : (a a' : ∣ A ∣) → ∣_∣f a → ∣_∣f a' → ♭ (homo A a a') ⇒Glob
open _⇒Glob

{-

ΠG : (A : Glob)(B : A ⇒Glob) → Glob
ΠG A B = 
  record 
  { ∣_∣ = (a : ∣ A ∣) → ∣ B ∣f a
  ; homo = λ f g → ♯ ΠG {!Π!} (homof B {!!} {!!} {!!} {!!}) -- ♯ Π ∣ A ∣ (λ a →  Π ∣ A ∣ (λ a' → ΠG (♭ (homo A a a')) {!homof a a'!}))
  }
-}
-- homof B