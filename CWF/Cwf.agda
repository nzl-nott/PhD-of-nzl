open import Level
open import Relation.Binary.PropositionalEquality as PE hiding (refl ; sym ; trans; isEquivalence; [_])

module Cwf (ext : Extensionality zero zero) where

open import Data.Nat
open import Data.Product renaming (<_,_> to ⟨_,_⟩)
open import Data.Rational
open import Function

open import Relation.Binary
open import Relation.Binary.Core using (_≡_; _≢_; _⇒_)
open import Data.Unit

import CategoryOfSetoid
module cos = CategoryOfSetoid ext
open cos

import HProp
module hp = HProp ext
open hp

-- Definition of Context:
-- Context are interpreted as setoids

Con = HSetoid

-- Context homomorphism (substitution)

ConHom = _⇉_

-----------------------------------------------
-- Types and Terms

record Ty (Γ : Con) : Set₁ where
  field
    fm     : ∣ Γ ∣ → HSetoid -- the setoid of types associated to Context Γ

-- substT p is the homomorphism between setoid of types, substitution of terms

    substT : {x y : ∣ Γ ∣} → 
             [ Γ ] x ≈ y →
             ∣ fm x ∣ → ∣ fm y ∣
    subst* : ∀{x y : ∣ Γ ∣}  -- substT respect the equality
             (p : [ Γ ] x ≈ y)
             {a b : ∣ fm x ∣} →
             [ fm x ] a ≈ b →
             [ fm y ] substT p a ≈ substT p b

-- beta equality

    refl*  : ∀(x : ∣ Γ ∣)
             (a : ∣ fm x ∣) → 
             [ fm x ] substT [ Γ ]refl a ≈ a
    trans* : ∀{x y z : ∣ Γ ∣}
             (p : [ Γ ] x ≈ y)
             (q : [ Γ ] y ≈ z)
             (a : ∣ fm x ∣) → 
             [ fm z ] substT q (substT p a) ≈ substT ([ Γ ]trans p q) a

-- the two proof-irrelevance lemmas for substT

  substT-pi : ∀{x y : ∣ Γ ∣}
              {p q : [ Γ ] x ≈ y}
              {a : ∣ fm x ∣} → [ fm y ] substT p a ≈ substT q a
  substT-pi {x} {y} {p} {q} {a} = reflexive (fm y) (PI Γ (λ x → substT x a))

  substT-pi' : ∀{x : ∣ Γ ∣}
               {p : [ Γ ] x ≈ x}
               {a : ∣ fm x ∣} → [ fm x ] substT p a ≈ a
  substT-pi' {x} {p} {a} = [ fm x ]trans substT-pi (refl* x a)

-- simplify proofs of trans of inverse equality (groupoid)

  trans-inv-l : ∀{x y z : ∣ Γ ∣}
              (p : [ Γ ] x ≈ y)
              (a : ∣ fm x ∣) → 
              [ fm x ] substT ([ Γ ]sym p) (substT p a) ≈ a
  trans-inv-l {x} p a = [ fm x ]trans (trans* p ([ Γ ]sym p) a) substT-pi'

  trans-inv-r : ∀{x y z : ∣ Γ ∣}
              (p : [ Γ ] y ≈ x)
              (a : ∣ fm x ∣) → 
              [ fm x ] substT p (substT ([ Γ ]sym p) a) ≈ a
  trans-inv-r {x} p a = [ fm x ]trans (trans* ([ Γ ]sym p) p a) substT-pi'

open Ty renaming (substT to [_]subst; subst* to [_]subst*; fm to [_]fm ;
                  refl* to [_]refl* ; trans* to [_]trans*; substT-pi to [_]substT-pi ;
                  substT-pi' to [_]substT-pi' ; trans-inv-l to [_]trans-inv-l;
                  trans-inv-r to [_]trans-inv-r)

-- Type substitution


_[_] : ∀ {Γ Δ : Con} → Ty Δ → Γ ⇉ Δ → Ty Γ
_[_] {Γ} {Δ} A f
     = record
     { fm     = fm ∘ fn
     ; substT = substT ∘ resp
     ; subst* = subst* ∘ resp
     ; refl*  = λ _ _ → substT-pi'
     ; trans* = λ {x} {y} {z} p q a → 
                [ fm (fn z) ]trans (trans* (resp p) (resp q) a) substT-pi
     }
     where 
       open Ty A
       open _⇉_ f

-- verification of functor laws (do we have extensional equality for record types? or eta equality?)

Fid : {Γ : Con}{A : Ty Γ} → A [ idCH ] ≡ A
Fid = {!A!}

Fcomp : {Γ Δ Φ : Con}{A : Ty Γ}(f : Δ ⇉ Γ)(g : Φ ⇉ Δ) → A [ f ∘c g ] ≡ A [ f ] [ g ]
Fcomp f g = {!!} 

record Tm {Γ : Con}(A : Ty Γ) : Set where
  field
    tm    : (x : ∣ Γ ∣) → ∣ [ A ]fm x ∣
    respt : ∀{x y : ∣ Γ ∣} → 
            (p : [ Γ ] x ≈ y) → 
            [ [ A ]fm y ] [ A ]subst p (tm x) ≈ tm y

open Tm renaming (tm to [_]tm ; respt to [_]respt)

-- Term substitution

_[_]m : ∀ {Γ Δ : Con}{A : Ty Δ} → Tm A → (f : Γ ⇉ Δ) → Tm (A [ f ])
_[_]m t f = record 
          { tm = [ t ]tm ∘ [ f ]fn
          ; respt = [ t ]respt ∘ [ f ]resp 
          }

-- to do: verification

Fidm : {Γ : Con}{A : Ty Γ}{t : Tm A} → subst (λ x → Tm x) Fid (t [ idCH ]m) ≡ t
Fidm = {!!}

Fcompm : {Γ Δ Φ : Con}{A : Ty Γ}{t : Tm A}(f : Δ ⇉ Γ)(g : Φ ⇉ Δ) → subst (λ x → Tm x) (Fcomp f g) (t [ f ∘c g ]m) ≡ t [ f ]m [ g ]m
Fcompm f g = {!!} 

----------------------------------------------------
-- Context

-- terminal object: empty context

● : Con
● = record {
      Carrier = ⊤;
      _≈h_    = λ _ _ → ⊤';
      refl    = tt;
      sym     = λ _ → tt;
      trans   = λ _ _ → tt }


-- empty substitution

⋆ : {Δ : Con} → Δ ⇉ ●
⋆ = record 
      { fn = λ _ → tt
      ; resp = λ _ → tt }


-- the empty substitution is unique

uniqueHom : ∀(Δ : Con) → (f : Δ ⇉ ●) → f ≡ ⋆
uniqueHom Δ f = PE.refl


-- context comprehension
 

-- To implement this is because I found Agda does not support lambda pattern matching for implicit arguments (though I found a patch on the Internet) 

_&'_ : (Γ : Con) → Ty Γ → HSetoid'
Γ &' A = record 
       { Carrier = Σ[ x ∶ ∣ Γ ∣ ] ∣ fm x ∣
       ; _≈h_  = λ{(x , a) (y , b) → 
                  Σ'[ p ∶ x ≈h y ] [ fm y ] substT p a ≈h b}
       ; refl  = λ {(a , b) → refl , refl* a b}
       ; sym   = λ {(x , a) (y , _) (p , q) → 
                 sym p , 
                 [ fm x ]trans (subst* (sym p) ([ fm y ]sym q)) (trans-inv-l {_} {_} {y} p a) } 
       ; trans = λ {(_ , a) _ (z , _) (p , q) (m , n) →
                 trans p m , 
                 [ fm z ]trans ([ fm z ]trans ([ fm z ]sym (trans* p m a)) (subst* m q)) n }
       }
       where 
         open HSetoid Γ
         open Ty A     

-- this is what we use 

_&_ : (Γ : Con) → Ty Γ → Con
Γ & A = transVariant (Γ &' A)


-- pairing operation

_,,_ : {Γ Δ : Con}{A : Ty Δ}(f : Γ ⇉ Δ) → (Tm (A [ f ])) → Γ ⇉ (Δ & A)
f ,, t = record 
         { fn = ⟨ [ f ]fn , [ t ]tm ⟩
         ; resp = ⟨ [ f ]resp , [ t ]respt ⟩
         }

-- projections

fst : {Γ Δ : Con}{A : Ty Δ} → Γ ⇉ (Δ & A) → Γ ⇉ Δ
fst f = record 
        { fn = proj₁ ∘ [ f ]fn
        ; resp = proj₁ ∘ [ f ]resp 
        }


snd : {Γ Δ : Con}{A : Ty Δ} → (f : Γ ⇉ (Δ & A)) → Tm (A [ fst {A = A} f ])
snd f = record 
        { tm = proj₂ ∘ [ f ]fn
        ; respt = proj₂ ∘ [ f ]resp 
        }


_^_ : {Γ Δ : Con}(f : Γ ⇉ Δ)(A : Ty Δ) → Γ & A [ f ] ⇉ Δ & A
f ^ A = record 
        { fn = ⟨ [ f ]fn ∘ proj₁ , proj₂ ⟩
        ; resp = ⟨ [ f ]resp ∘ proj₁ , proj₂ ⟩
        }


---------------------------
-- Π types (object level)



Π : {Γ : Con}(A : Ty Γ)(B : Ty (Γ & A)) → Ty Γ
Π {Γ} A B = record 
      { fm = λ x → record
           { Carrier = Σ[ fn ∶ ((a : ∣ [ A ]fm x ∣) → ∣ [ B ]fm (x , a) ∣) ]
                       ((a b : ∣ [ A ]fm x ∣)(p : [ [ A ]fm x ] a ≈ b) → [ [ B ]fm (x , b) ] [ B ]subst ([ Γ ]refl , [ [ A ]fm x ]trans ([ A ]refl* x a) p) (fn a) ≈ fn b ) -- this part is more complicated than the one on the paper (the long term is just p on the paper)

           ; _≈h_    = λ{(f , _) (g , _) → ∀'[ a ∶ _ ] [ [ B ]fm (x , a) ] f a ≈h g a }
           ; refl    = λ a → [ [ B ]fm (x , a) ]refl 
           ; sym     = λ f a → [ [ B ]fm (x , a) ]sym (f a)
           ; trans   = λ f g a → [ [ B ]fm (x , a) ]trans (f a) (g a)
           }
      ; substT = λ {x} {y} p → 
                   λ{(f , rsp) →  
                        (λ a → [ B ]subst (p , [ A ]trans-inv-r {_} {_} {y} p a) (f ([ A ]subst ([ Γ ]sym p) a))) ,                                 -- this is g
                        (λ a b q → let a' = [ A ]subst ([ Γ ]sym p) a in 
                                   let b' = [ A ]subst ([ Γ ]sym p) b in
                                   let H : [ [ B ]fm (x , b') ] [ B ]subst ([ Γ ]refl , [ [ A ]fm x ]trans ([ A ]refl* _ _) ([ A ]subst* _ q)) (f a') ≈ f b'
                                       H = {!!} in {![ B ]substT-pi'!})     
                                              -- this is g-resp
                                 }
      ; subst* = λ _ q _ → [ B ]subst* _ (q _)
      ; refl* = λ {x (f , rsp) a → {!rsp!} } -- [ [ B ]fm (x , a) ]trans {![ B ]subst*!} ([ B ]refl* _ (f a))
      ; trans* = {!!} 
      }