{-# OPTIONS --type-in-type #-}

import Level
open import Relation.Binary.PropositionalEquality as PE hiding (refl ; sym ; trans; isEquivalence; [_])

module Cwf-quotient (ext : Extensionality Level.zero Level.zero) where

open import Data.Unit
open import Function
open import Data.Product


-- importing other CWF files

import Cwf

open Cwf ext

import CategoryOfSetoid
module cos' = CategoryOfSetoid ext
open cos'

import HProp
module hp' = HProp ext
open hp'

import Cwf-ctd
module cc = Cwf-ctd ext
open cc

-- propositional univalence

Pu : HSetoid
Pu = record
      { Carrier = HProp
      ; _≈h_    = _⇄_
      ; refl    = id , id 
      ; sym     = λ {(a , b) →(b , a)}
      ; trans   = λ {(a , b) (a' , b') → (a' ∘ a) , (b ∘ b')}
      }


⟦Prop⟧ : Ty ●
⟦Prop⟧ = record { fm = λ x → Pu; substT = λ x' x0 → x0; subst* = λ p x' → x'; refl* = λ x a → id , id; trans* = λ p q a → id , id }

⟦Prf⟧ : Ty (● & ⟦Prop⟧)
⟦Prf⟧ = record { fm = λ {(_ , p) → 
                 record
                 { Carrier = ⊤
                 ; _≈h_    = λ x x' → ⊤'
                 ; refl    = tt
                 ; sym     = id
                 ; trans   = λ x' x0 → x'
                 } }
               ; substT = λ x' x0 → x0; subst* = λ p x' → x'; refl* = λ x a → a; trans* = λ p q a → a }

-- several isomorphisms

isoPi1 : {Γ : Con}{A : Ty Γ}{B : Ty (Γ & A)} → Tm {Γ & A} B → Tm (Π A B)
isoPi1 (tm: tm resp: respt) = tm: (λ x → (λ a → tm (x , a)) , (λ a b p → respt _)) resp: (λ p x' → respt _)



-- Do I need to define equivalence relation or follow the way on the paper by Martin Hoffmann ?

Equiv : {Γ : Con}(A : Ty Γ) → Ty Γ
Equiv A = Π A (Π (A [ fst& {A = A} ]) (⟦Prop⟧ [ (fn: (λ x → tt) resp: (λ x' → tt)) ]))

module Q (Γ : Con)(A : Ty Γ)(R : Tm (Equiv A)) where

{-
  ⟦Q⟧ : Ty Γ
  ⟦Q⟧ = record 
    { fm = λ γ → record
         { Carrier = ∣ [ A ]fm γ ∣
         ; _≈h_ = λ x x' → proj₁ (proj₁ ([ R ]tm γ) x) x'
         ; refl = [ _ ]refl
         ; sym = [ _ ]sym
         ; trans = [ _ ]trans
         }
    ; substT = {!!}
    ; subst* = {!!}
    ; refl* = {!!}
    ; trans* = {!!}
    }

-}