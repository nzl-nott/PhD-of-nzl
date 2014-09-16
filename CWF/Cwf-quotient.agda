{-# OPTIONS --type-in-type #-}

import Level
open import Relation.Binary.PropositionalEquality as PE hiding (refl ; sym ; trans; isEquivalence; [_])

module CwF-quotient (ext : Extensionality Level.zero Level.zero) where

open import Data.Unit
open import Function
open import Data.Product

-- open import HProp ext

-- open import CategoryOfSetoid ext

-- open import CwF-setoid ext


open import CwF-ctd ext

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
⟦Prop⟧ = record { fm = λ x → Pu; substT = λ x' x0 → x0; subst* = λ p x' → x'; refl* = λ x a → id , id; trans* = λ _ → id , id }

⟦Prf⟧ : Ty (● & ⟦Prop⟧)
⟦Prf⟧ = record { fm = λ {(_ , p) → 
                 record
                 { Carrier = ⊤
                 ; _≈h_    = λ x x' → ⊤'
                 ; refl    = tt
                 ; sym     = id
                 ; trans   = λ x' x0 → x'
                 } }
               ; substT = λ x' x0 → x0; subst* = λ p x' → x'; refl* = λ x a → a; trans* = λ a → a }

-- several isomorphisms

isoPi1 : {Γ : Con}{A : Ty Γ}{B : Ty (Γ & A)} → Tm {Γ & A} B → Tm (Π A B)
isoPi1 (tm: tm resp: respt) = tm: (λ x → (λ a → tm (x , a)) , (λ a b p → respt _)) resp: (λ p x' → respt _)



PropRel : {Γ : Con}(A : Ty Γ) → Ty Γ
PropRel A = Π A (Π (A [ fst& {A = A} ]T) (⟦Prop⟧ [ (fn: (λ x → tt) resp: (λ x' → tt)) ]T))

{-
Refl : {Γ : Con}(A : Ty Γ) → Tm (PropRel A) → Ty Γ
Refl A rel = ?

Equiv :  {Γ : Con}(A : Ty Γ) → Ty Γ
Equiv A = Σ'' (PropRel A)  {!!}
-}          

{-
stack overflow
Refl : {Γ : Con}(A : Ty Γ) → Tm (PropRel A) → Ty Γ
Refl A rel = ?
-}


module Q (Γ : Con)(A : Ty Γ)(R : Tm (PropRel A)) where
  ⟦Q⟧ : Ty Γ
  ⟦Q⟧ = record 
    { fm = λ γ →
         record
         { Carrier = ∣ [ A ]fm γ ∣
         ; _≈h_ = λ m n → proj₁ (proj₁ ([ R ]tm γ) m) n
         ; refl = λ {x} → {!!} -- [ _ ]refl
         ; sym = {!!} -- [ _ ]sym
         ; trans = {!!} -- [ _ ]trans
         }
    ; substT = [ A ]subst
    ; subst* = λ p x₁ → {![ A ]subst* p !}
    ; refl* = {!!}
    ; trans* = {!!}
    }



-- The mechanism used in Martin Hofmann's Paper

record Prop-Uni (Γ : Con) : Set where
  field
    prf : Ty Γ
    uni : ∀ γ x y → [ [ prf ]fm γ ] x ≈h y ≡ ⊤'
open Prop-Uni

-- The Equality Type


Id : {Γ : Con}(A : Ty Γ) → Ty (Γ & A & (A [ fst& {Γ} {A} ]T))
Id A
   = record 
       { fm = λ {((x , a) , b) →  record
         { Carrier = [ [ A ]fm x ] a ≈ b
         ; _≈h_ = λ x₁ x₂ → ⊤' -- it is : Prop
         ; refl = λ {x₁} → tt
         ; sym = λ x₂ → tt
         ; trans = λ x₂ x₃ → tt
         } }
       ; substT = λ {x} {y} → λ {((p , q) , r) x₂ → 
                    [ [ A ]fm (proj₁ (proj₁ y)) ]trans ([ [ A ]fm (proj₁ (proj₁ y)) ]sym q)
                   ([ [ A ]fm (proj₁ (proj₁ y)) ]trans ([ A ]subst* p x₂)
                     r)}
       ; subst* = λ p x₁ → tt
       ; refl* = λ x a → tt
       ; trans* = λ _ → tt }


-- Is it correct to write  Tm A → Tm B for dependent types?


Id-is-prop : {Γ : Con}(A : Ty Γ) → Prop-Uni (Γ & A & (A [ fst& {Γ} {A} ]T))
Id-is-prop A = record { prf = Id A ; uni = λ γ x y → PE.refl }

{-
record Quo {Γ : Con}(A : Ty Γ)(R : Prop-Uni (Γ & A & (A [ fst& {Γ} {A} ]T))) : Set where
  field
    Q : Ty Γ
    [_] : Tm A → Tm Q
    Q-elim : ∀ (B : Ty Γ)
                 (M : Tm {Γ & A} (B [ fst& {Γ} {A} ]T))
                 (N : Tm Q)
                 (H : Tm {Γ & A & A [ fst& {Γ} {A} ]T & prf R} (prf (Id-is-prop B) [ fst& {Γ & A & A [ fst& {Γ} {A} ]T} {prf R} ]T)) -- (prf (Id-is-prop (B [ fst& {Γ} {A} ]T)))
               → Tm B

-}