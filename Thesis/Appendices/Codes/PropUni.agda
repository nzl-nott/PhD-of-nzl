
{-

This file contains a proof of follows:

Propositional univalence => All quotients are effective

-}

module PropUni where

open import Data.Product
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Quotient

Prp = Set

_⇔_ : (A B : Prp) → Prp
A ⇔ B = (A → B) × (B → A)

module PuImpEff
-- several axioms
  (uni : (A : Prp)(a b : A) → a ≡ b)
  (PropUni₁ : ∀ {p q : Prp} → (p ⇔ q) → p ≡ q)

-- this PropUni₂ is trivial inhabited by two identity function
  (PropUni₂ : ∀ {p q : Prp} → (p ≡ q) → p ⇔ q)

  (S : Setoid _ _)
  (QS : QuSig S)
  (QU : Qu QS)
    where

  open Setoid S renaming (Carrier to A ; refl to Arefl ; trans to Atrans ; sym to Asym)
  open QuSig QS
  open Qu QU
  

-- since the level is not taken into account when defining quotient lifting, we have to postulate extra functions
  
  postulate 
    lift₁ : { B : Q → Set₁}  → 
             (f : (a : A) → (B [ a ])) → 
             ((a a' : A) → (p : a ≈ a') → 
             subst B (sound p)  (f a)  ≡  f a') → 
             (c : Q) → B c

  postulate
    liftok₁ : ∀ {B a f q} → lift₁ {B} f q [ a ]  ≡ f a



  substIrr1 : ∀ {P : Prp}{A : Set}{x y : A}(eq : x ≡ y) → subst (λ _ → Prp) eq P → P
  substIrr1 {P} {A} {.y} {y} _≡_.refl sp = sp

  
  substIrr2 : ∀ {P : Prp}{A : Set}{x y : A}(eq : x ≡ y) → P → subst (λ _ → Prp) eq P
  substIrr2 {P} {A} {.y} {y} _≡_.refl sp = sp

  subEq : {X : Set}
         {m n : X}
         {PA PB : Prp} → 
         (eq : m ≡ n) → 
         PA ⇔ PB → 
         subst (λ _ → Prp) eq PA ≡ PB
  subEq eq (lr , rl) = PropUni₁ ((λ x → lr (substIrr1 eq x)) , (λ x → substIrr2 eq (rl x)))


-- the effectiveness of quotients

  compl : (a b : A) → [ a ] ≡ [ b ] → a ≈ b
  compl a b eq = subst (λ x → x) (trans (sym (comp-P a)) (trans cong-P^ (comp-P b))) refl-a
    where
      P : A → Prp
      P x = a ≈ x

      lem : {x y : A} →
             (p : x ≈ y) →
             P x ⇔ P y
      lem p = (λ x' → Atrans x' p) , (λ x' → Atrans x' (Asym p))

      P^ : Q → Prp
      P^ = lift₁ P (λ _ _ p → subEq (sound p) (lem p))

      cong-P^ : P^ [ a ] ≡ P^ [ b ]
      cong-P^ = cong P^ eq

      refl-a : P a
      refl-a = Arefl

      comp-P : ∀ x → P^ [ x ] ≡ P x
      comp-P x = liftok₁ {λ _ → Prp} {x}



  EQ : QuE QU
  EQ = record { complete = λ {a} {b} → compl a b }
