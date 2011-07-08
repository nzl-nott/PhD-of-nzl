
{-# OPTIONS --universe-polymorphism #-}

module Quotient' where

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

-- 2.1,2,3
-- 
-- Quotient signature
--

-- To have shorter notation

Setoid = Setoid' zero zero

-- Generalisation of sound

Sound : ∀ {A B : Set}(_∼_ : A → A → Set)(_≈_ : B → B → Set)(f : A → B) → Set
Sound {A} {B} _∼_ _≈_ f = ∀ {a b : A} → a ∼ b → f a ≡ f b


record PreQu (S : Setoid) : Set₁ where
             constructor
               Q:_[]:_sound:_
             private
               A   = Carrier S
               _∼_ = _≈_ S
             field
               Q     : Set
               [_]   : A → Q
               sound : Sound _∼_ _≡_ [_]
              
open PreQu renaming (Q to Q' ; [_] to [_]' ; sound to sound')


-- 
-- Different quotient definitions over a quotient signature
--


-- 2.4
-- Quotient by dependent lifting
--
-- if ~ is a congruence for f : S → B then f can be lifted to Q → B

record Qu {S : Setoid} (QS : PreQu S) : Set₁ where
              constructor
                lift:_Ok:_
              private 
                A      = Carrier S
                _∼_    = _≈_ S
                Q      = Q' QS
                [_]    = [_]' QS
                sound  : ∀ {a b : A} → (a ∼ b) → [ a ] ≡ [ b ]
                sound  = sound' QS
              field
                qelim   : {B : Q → Set}
                        → (f : (a : A) → B [ a ])
                        → ((a b : A) → (p : a ∼ b) → subst B (sound p) (f a)  ≡  f b)
                        → (q : Q) → B q
                qelim-β : ∀ {B a f q} → qelim {B} f q [ a ]  ≡ f a

-- proof qelim-β -> qelimIrr _≅_

open Qu

qelimIrr : {S : Setoid}{PQ : PreQu S}(x : Qu PQ) 
         → (∀ {B a f q q'} → qelim x {B} f q ([_]' PQ a) ≡ qelim x {B} f q' ([_]' PQ a ))
qelimIrr x {B} {a} {f} {q} {q'} = trans (qelim-β x {B} {a} {f} {q}) (sym (qelim-β x {B} {a} {f} {q'}))


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
              private A      = Carrier S
                      _∼_    = _≈_ S
                      Q      = Q' PQ
                      [_]    = [_]' PQ
              field
                lift   : {B : Set}
                       → (f : A → B)
                       → Sound _∼_ _≡_ f
                       → Q → B
                liftok : ∀ {B a f q} → lift {B} f q [ a ]  ≡ f a
                -- quotient induction
                qind : (P : Q → Set)  
                       → (∀ x → (p p' : P x) → p ≡ p')
                       → (∀ a → P [ a ]) 
                       → (∀ x → P x )

open QuH


-- 2.3
-- Normal forms
-- 
record Nf {S : Setoid} (PQ : PreQu S) : Set₁ where
       constructor emb:_compl:_stable:_
       private A     = Carrier S
               _∼_   = _≈_ S
               Q     = Q' PQ
               [_]   = [_]' PQ
       field
         emb    : Q → A                           -- embedding, choice of a representative for each class
         compl  : ∀ a → emb [ a ] ∼ a              -- completeness (because it implies the implication: [a]≡[b] ⇒ a∼b and, in presence of stability, is equivalent to it)
         stable : ∀ x → [ emb x ]  ≡ x             -- stability
open Nf

-- SECTION 3
--
-- Translation between quotient definitions
--


nf2quE : {S : Setoid} → {PQ : PreQu S} → {QU : Qu PQ} → (Nf PQ) → (QuE QU)
nf2quE {S} {PQ} {QU} nf = record { exact =  λ {a} {b} [a]≡[b] → ⟨ compl₀ a ⟩₀    ▶₀    subst (λ x → x ∼ b) (emb₀ ⋆ ⟨ [a]≡[b] ⟩) (compl₀ b) }
                          where
                          private A      = Carrier S
                                  _∼_    = _≈_ S
                                  Q      = Q' PQ
                                  [_]    = [_]' PQ
                                  emb₀   = emb    nf
                                  compl₀ = compl  nf
                                  ⟨_⟩₀    : Symmetric _∼_
                                  ⟨_⟩₀    = symmetric S
                                  _▶₀_    : Transitive _∼_
                                  _▶₀_    = transitive S 

-- Remark that stability would be a consequence of the surjectivity of [_], soundness and completeness. However, the map [_] is not required to be surjective. (So Qu2nf is wrong?)

nf2qu : {S : Setoid} → {PQ : PreQu S} → (Nf PQ) → (Qu PQ)
nf2qu {S} {PQ} nf = 
        record {
        qelim    =  λ {B} f q a⁻ → subst B (stable₀ a⁻) (f (emb₀ a⁻));   -- λ {B} f q a⁻ → lift' PQ f q a⁻ (subst (λ x → Image [_]₀ ∋ x) (stable₀ a⁻) (im (emb₀ a⁻))) ;
        qelim-β  = λ {B} {a} {f} {q} → substIrr B (stable₀ [ a ]) (sound (compl₀ a))  (f (emb₀ [ a ])) ▶ q _ _ (compl₀ a)
--  ;        qelimIrr = refl
        }
        where   S₀      = Carrier S
                _∼_     = _≈_ S
                [_]    = [_]' PQ
                sound  : ∀ { a b : S₀} → a ∼ b → [ a ] ≡ [ b ]
                sound  = sound'  PQ
                compl₀  = compl  nf
                stable₀ = stable nf
                emb₀    = emb    nf


quH2qu : {S : Setoid} → {PQ : PreQu S} → (QuH PQ) → (Qu PQ)
quH2qu {S} {PQ} quh = 
             record { qelim    = λ {B} f q c →  lift₂ {B} f q c
                    ; qelim-β  = λ {B} {a} {f} {q} → liftok₁ {B} a f q
--                    ; qelimIrr = λ {B} {a} {f} {q} {q'} → trans (liftok₁ {B} a f q ) (sym (liftok₁ {B} a f q')) 
                    }
             where
               
               -- notation
               A      = Carrier S
               _∼_    = _≈_ S
               Q      = Q' PQ
               [_]    = [_]' PQ
               sound  : ∀ {a b : A} → (a ∼ b) → [ a ] ≡ [ b ]
               sound  = sound' PQ
               lift₀ : { B : Set } → (f : A → B) → ((a a' : A) → (a ∼ a') →  (f a)  ≡  f a') → Q → B
               lift₀ = lift quh 
               liftok₀ : ∀ {B a f q}    → lift₀ {B} f q [ a ]  ≡ f a 
               liftok₀ = liftok quh
               qind₀ = qind quh
               -- the dependent function f is made independent
               indep : {B : Q → Set}  → ((a : A) → B [ a ]) → A → Σ Q B
               indep f a = [ a ] , f a
               indepok :  {B : Q → Set}  → (f : (a : A) → B [ a ]) 
                                          → ((a a' : A) → (p : a ∼ a') → subst B (sound p)  (f a)  ≡  f a') 
                                          → (a a' : A) 
                                          → (a ∼ a') 
                                          → indep {B} f a  ≡  indep f a'          
               indepok f q a a' p = trans (cong_,_ [ a ] [ a' ] (sound p) (f a)) (cong (λ b → [ a' ] , b) (q a a' p))

               -- quotient induction                     
               qind₁   :  {B : Q → Set}  → (f : (a : A) → B [ a ]) 
                                          → (q : (a a' : A) → (p : a ∼ a') → subst B (sound p)  (f a)  ≡  f a') 
                                          → ∀ (c : Q) → proj₁ {zero} {zero} {Q} {B} (lift₀ (indep f) (indepok f q) c) ≡ c
               qind₁ {B} f q = qind₀ P heredity base 
                                          where 
                                          P : Q → Set
                                          P c = proj₁ {zero} {zero} {Q} {B} (lift quh (indep f) (indepok f q) c) ≡ c
                                          heredity : ∀ x → (p p' : P x) → p ≡ p' 
                                          heredity     x    p p'          = ≡-prfIrr ((lift₀ (indep f) (indepok f q) x)₁) x p p'  
                                          base : ∀ a → P [ a ]
                                          base a = cong proj₁ liftok₀

               -- definitions of lift and liftok
               lift₁ : { B : Q → Set } → (f : (a : A) → (B [ a ])) → ((a a' : A) → (p : a ∼ a') → subst B (sound p)  (f a)  ≡  f a') → A → Σ Q B 
               lift₁ f q a = lift₀ (indep f) (indepok f q) [ a ]

               lift₂  : { B : Q → Set }
                        → (f : (a : A) → (B [ a ]))
                        → ((a a' : A) → (p : a ∼ a') → subst B (sound p)  (f a)  ≡  f a')
                        → (c : Q) → B c 
               lift₂ {B} f q c =  subst B (qind₁ f q c) (proj₂ {zero} {zero} {Q} {B} (lift₀ (indep f) (indepok f q)  c))

               liftok₁  : ∀ {B} a f q    → lift₂ {B} f q [ a ]  ≡ f a
               liftok₁   {B} a f q = trans (substIrr B (qind₁ f q [ a ]) 
                                                       (cong-proj₁ {Q} {B} (lift₁ f q a) (indep f a) liftok₀) 
                                                            (proj₂ {zero} {zero} {Q} {B} (lift₁ f q a)))
                                                       (cong-proj₂ {Q} {B} (lift₁ f q a) (indep f a) liftok₀ )


Nf2QuH : {S : Setoid} → {PQ : PreQu S} → (Nf PQ) → (QuH PQ)
Nf2QuH {S} {Q: Q []: [_] sound: sound} (emb: ⌜_⌝ compl: compl stable: stable) = 
  record { lift = λ f x x' → f ⌜ x' ⌝
         ; liftok = λ {B} {a} {f} {q} → q  ⌜ [ a ] ⌝ a (compl a)
         ; qind = λ P irr f → λ x0 → subst P (stable x0) (f ⌜ x0 ⌝) 
         }











-- It is impossible : qu to quH

subFix : ∀ {A : Set}{c d : A}(x : c ≡ d)(B : Set)(p : B) → subst (λ _ → B) x p ≡ p
subFix refl B p' = refl

sFlem : ∀ {A : Set}(P : A → Set)(a : A)(eq : a ≡ a)(x : P a) → subst P eq x ≡ x
sFlem P a refl x = refl


subst' : ∀ {A : Set}{a b : A}(P : A → Set)(eq : a ≡ b) → P a → P b
subst' P refl p = p


qu2quH : {S : Setoid} → {PQ : PreQu S} → (Qu PQ) → (QuH PQ)
qu2quH {S} {Q: Q []: [_] sound: sound} (lift: lift Ok: ok) = record 
              { lift = λ {B} f x x' → lift {λ _ → B} f (λ a a' p → trans (subFix (sound p) B (f a)) (x a a' p)) x'
              ; liftok = λ {B} {a} {f} {q} → ok {λ _ → B} {a} {f} {λ a' a0 p → trans (subFix (sound p) B (f a')) (q a' a0 p)}
              ; qind = λ P irr f → λ x0 → lift {P} (λ a → f a) (λ a b p → irr [ b ] (subst P (sound p) (f a)) (f b)) x0
              } 