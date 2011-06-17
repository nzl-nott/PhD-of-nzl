
{-# OPTIONS --universe-polymorphism #-}

module Quotient'' where

open import Relation.Binary renaming (Setoid to Setoid')
open import Relation.Binary.Core
open Setoid renaming (refl to reflexive; sym to symmetric; trans to transitive)
open import Relation.Binary.PropositionalEquality.Core

open import Data.Nat
open import Data.Nat.Properties

open import Data.Product

open import Level using (Level ; zero)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Project modules
open import ThomasProperties


-- Li Nuo's transformed version of congurence laws

_by_ : ∀{p q}{A : Set p}{B : Set q}{a b : A} → a ≡ b → (f : A → B) → f a ≡ f b
refl by f = refl


-- 2.1,2,3
-- 
-- Quotient signature
--

-- To have shorter notation

Setoid = Setoid' zero zero

record PreQu (S : Setoid) : Set₁ where
             constructor
               Q:_[]:_sound:_
             private
               A   = Carrier S
               _∼_ = _≈_ S
             field
               Q     : Set
               [_]   : A → Q
               sound : ∀ {a b : A} → a ∼ b → [ a ] ≡ [ b ]
              
open PreQu renaming (Q to Q' ; [_] to [_]' ; sound to sound')


-- 
-- Different quotient definitions over a quotient signature
--


-- 2.4
-- Quotient by dependent lifting
--
-- if ~ is a congruence for f : S → B then f can be lifted to Q → B

Sound : {S : Setoid} (QS : PreQu S) → (Q' QS → Set) → Set
Sound {S} (Q: Q []: [_] sound: sound) B = Σ[ f ∶ ((a : A) → B [ a ]) ] ((a b : A) → (p : a ∼ b) → subst B (sound p) (f a)  ≡  f b)
  where
    A      = Carrier S
    _∼_    = _≈_ S

record Qu {S : Setoid} (QS : PreQu S) : Set₁ where
              constructor
                qelim:_qelim-β:_
              private 
                A      = Carrier S
                _∼_    = _≈_ S
                Q      = Q' QS
                [_]    = [_]' QS
                sound  : ∀ {a b : A} → (a ∼ b) → [ a ] ≡ [ b ]
                sound  = sound' QS
              field
                qelim   : {B : Q → Set}
                        → Sound QS B
                        → (q : Q) → B q
                qelim-β : ∀ {B a f q} → qelim {B} (f , q) [ a ]  ≡ f a -- β-law

-- proof qelim-β -> qelimIrr _≅_

open Qu

qelimIrr : {S : Setoid}{PQ : PreQu S}(x : Qu PQ) 
         → (∀ {B a f q q'} → qelim x {B} (f , q) ([_]' PQ a) ≡ qelim x {B} (f , q') ([_]' PQ a ))
qelimIrr x {B} {a} {f} {q} {q'} = (qelim-β x {B} {a} {f} {q}) ▶ (sym (qelim-β x {B} {a} {f} {q'}))


-- 2.5
-- Exact quotients
--

record QuE {S : Setoid} {PQ : PreQu S} (QU : Qu PQ) : Set₁ where
       private 
         A      = Carrier S
         _∼_    = _≈_ S
         [_]    = [_]' PQ
       field
         exact : ∀ {a b : A} → [ a ] ≡ [ b ] → a ∼ b

open QuE


-- 2.4
-- Non-dependent lift à la Hofmann
--

record QuH {S : Setoid} (PQ : PreQu S) : Set₁ where
       constructor
         lift:_lift-β:_qind:_
       private 
         A      = Carrier S
         _∼_    = _≈_ S
         Q      = Q' PQ
         [_]    = [_]' PQ
       field
         lift   : {B : Set}
                → (f : A → B)
                → ((a b : A) → (a ∼ b) → f a  ≡  f b)
                → Q → B
         lift-β : ∀ {B a f q} → lift {B} f q [ a ]  ≡ f a -- β law
         -- quotient induction
         qind : (P : Q → Set)  
              → (∀ x → (p p' : P x) → p ≡ p') -- Namely P is Q → Prop
              → (∀ a → P [ a ]) 
              → (∀ x → P x )

open QuH renaming (lift to lift' ; lift-β to lift-β')

-- 2.3
-- Definable quotients
-- 
record QuD {S : Setoid}(PQ : PreQu S) : Set₁ where
       constructor
         emb:_compl:_stable:_
       private 
         A     = Carrier S
         _∼_   = _≈_ S
         Q     = Q' PQ
         [_]   = [_]' PQ
       field
         emb    : Q → A                        -- embedding, choice of a representative for each class
         compl  : ∀ a → emb [ a ] ∼ a          -- completeness (because it implies the implication: [a]≡[b] ⇒ a∼b and, in presence of stability, is equivalent to it)
         stable : ∀ q → [ emb q ]  ≡ q         -- stability
open QuD

-- SECTION 3
--
-- Translation between quotient definitions
--


nf2quE : {S : Setoid}{PQ : PreQu S}{QU : Qu PQ} → (QuD PQ) → (QuE QU)
nf2quE {S} {Q: Q []: [_] sound: _} (emb: emb compl: compl stable: _) =
  record { exact =  λ {a} {b} [a]≡[b] → ⟨ compl a ⟩₀   ▶₀    subst (λ x → x ∼ b) (emb ⋆ ⟨ [a]≡[b] ⟩) (compl b) }
                          where
                          private A      = Carrier S
                                  _∼_    = _≈_ S
                                  ⟨_⟩₀    : Symmetric _∼_
                                  ⟨_⟩₀    = symmetric S
                                  _▶₀_    : Transitive _∼_
                                  _▶₀_    = transitive S 

-- Remark that stability would be a consequence of the surjectivity of [_], soundness and completeness. However, the map [_] is not required to be surjective.

qud2qu : {S : Setoid} → {PQ : PreQu S} → (QuD PQ) → (Qu PQ)
qud2qu {S} {Q: Q []: [_] sound: sound} (emb: emb compl: compl stable: stable) = 
        record 
        { qelim   = λ {B} f _ a⁻ → subst B (stable a⁻) (f (emb a⁻))
        ; qelim-β = λ {B} {a} {f} {q} → substIrr B (stable [ a ]) (sound (compl a))  (f (emb [ a ])) ▶ q _ _ (compl a)
        }


quH2qu : {S : Setoid} → {PQ : PreQu S} → (QuH PQ) → (Qu PQ)
quH2qu {S} {Q: Q []: [_] sound: sound} (lift: lift lift-β: β qind: qind) = 
        record 
        { qelim   = λ {B} → qelim₁ {B}
        ; qelim-β = λ {B} {a} {f} {q} → qelim-β₁ {B} a f q
        }
             where
               -- notation
               A      = Carrier S
               _∼_    = _≈_ S

               -- the dependent function f is made independent
               indep : {B : Q → Set}  → ((a : A) → B [ a ]) → A → Σ Q B
               indep f a = [ a ] , f a

               indepok :  {B : Q → Set} 
                       → (f : (a : A) → B [ a ]) 
                       → ((a a' : A) → (p : a ∼ a') → subst B (sound p) (f a) ≡ f a') 
                       → (a a' : A) 
                       → (a ∼ a') 
                       → indep {B} f a  ≡  indep f a'          
               indepok {B} f q a a' p = (cong_,_ [ a ] [ a' ] (sound p) (f a)) ▶ (cong (λ b → [ a' ] , b) (q a a' p))

               -- quotient induction                     
               qind₁   :  {B : Q → Set}
                       → (f : (a : A) → B [ a ]) 
                       → (q : (a a' : A) → (p : a ∼ a') → subst B (sound p) (f a)  ≡  f a') 
                       → ∀ (c : Q) → proj₁ (lift (indep f) (indepok f q) c) ≡ c
               qind₁ {B} f q = qind P heredity base 
                       where 
                         P : Q → Set
                         P c = proj₁ {_} {_} {Q} {B} (lift (indep f) (indepok f q) c) ≡ c
                         heredity : ∀ x → (p p' : P x) → p ≡ p' 
                         heredity     x    p p'          = ≡-prfIrr ((lift (indep f) (indepok f q) x)₁) x p p'  
                         base : ∀ a → P [ a ]
                         base a = cong proj₁ β


               lift₁ : {B : Q → Set} → (f : (a : A) → (B [ a ])) → ((a a' : A) → (p : a ∼ a') → subst B (sound p)  (f a)  ≡  f a') → A → Σ Q B 
               lift₁ f q a = lift (indep f) (indepok f q) [ a ]

               qelim₁  : { B : Q → Set }
                        → (f : (a : A) → (B [ a ]))
                        → ((a a' : A) → (p : a ∼ a') → subst B (sound p)  (f a)  ≡  f a')
                        → (c : Q) → B c 
               qelim₁ {B} f q c =  subst B (qind₁ f q c) (proj₂ {_} {_} {Q} {B} (lift (indep f) (indepok f q) c))

               qelim-β₁  : ∀ {B} a f q → qelim₁ {B} f q [ a ]  ≡ f a
               qelim-β₁ {B} a f q = (substIrr B (qind₁ f q [ a ]) 
                                              (cong-proj₁ {Q} {B} (lift₁ f q a) (indep f a) β) 
                                              (proj₂ {zero} {zero} {Q} {B} (lift₁ f q a))) ▶
                                    (cong-proj₂ {Q} {B} (lift₁ f q a) (indep f a) β )


QuD2QuH : {S : Setoid} → {PQ : PreQu S} → (QuD PQ) → (QuH PQ)
QuD2QuH {S} {Q: Q []: [_] sound: sound} (emb: ⌜_⌝ compl: compl stable: stable) = 
  record { lift = λ f _ x' → f ⌜ x' ⌝
         ; lift-β = λ {B} {a} {f} {q} → q  ⌜ [ a ] ⌝ a (compl a)
         ; qind = λ P irr f → λ x0 → subst P (stable x0) (f ⌜ x0 ⌝) 
         }



subFix : ∀ {A : Set}{c d : A}(x : c ≡ d)(B : Set)(p : B) → subst (λ _ → B) x p ≡ p
subFix refl B p' = refl


qu2quH : {S : Setoid} → {PQ : PreQu S} → (Qu PQ) → (QuH PQ)
qu2quH {S} {Q: Q []: [_] sound: sound} (qelim: qelim qelim-β: β) = record 
              { lift = λ {B} f x x' → qelim {λ _ → B} f (λ a a' p 
              → trans (subFix (sound p) B (f a)) (x a a' p)) x'
              ; lift-β = λ {B} {a} {f} {q} → β {λ _ → B} {a} {f} {λ a' a0 p 
              → trans (subFix (sound p) B (f a')) (q a' a0 p)}
              ; qind = λ P irr f → λ x0 
              → qelim {P} (λ a → f a) (λ a b p → irr [ b ] (subst P (sound p) (f a)) (f b)) x0
              } 