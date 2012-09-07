open import Level
open import Relation.Binary.PropositionalEquality as PE hiding (refl ; sym ; trans; isEquivalence; [_])

module Cwf (ext : Extensionality zero zero) where

open import Data.Product renaming (<_,_> to ⟨_,_⟩)
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
             ∣ fm x ∣ → 
             ∣ fm y ∣
    subst* : ∀{x y : ∣ Γ ∣}  -- substT respects the equality
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


-- the proof-irrelevance lemmas for substT

  subst-pi : ∀{x y : ∣ Γ ∣}
              {p q : [ Γ ] x ≈ y}
              {a : ∣ fm x ∣} → [ fm y ] substT p a ≈ substT q a
  subst-pi {x} {y} {p} {q} {a} = reflexive (fm y) (PI Γ (λ x → substT x a))

  subst-pi' : ∀{x : ∣ Γ ∣}
               {p : [ Γ ] x ≈ x}
               {a : ∣ fm x ∣} → [ fm x ] substT p a ≈ a
  subst-pi' = [ fm _ ]trans subst-pi (refl* _ _)

  subst-pi* : ∀{x y : ∣ Γ ∣}
                {p q : [ Γ ] x ≈ y}
                {a b : ∣ fm x ∣} → [ fm x ] a ≈ b → [ fm y ] substT p a ≈ substT q b
  subst-pi* eq = [ fm _ ]trans (subst* _ eq) subst-pi


-- simplify proofs of trans of inverse equality (including groupoid laws?)

  trans-refl : ∀{x y : ∣ Γ ∣}
              {p : [ Γ ] x ≈ y}{q : [ Γ ] y ≈ x}
              {a : ∣ fm x ∣} → 
              [ fm x ] substT q (substT p a) ≈ a
  trans-refl = [ fm _ ]trans (trans* _ _ _) subst-pi'

-- some more theorems
  
  subst-mir1 : ∀{x y : ∣ Γ ∣}
              {p : [ Γ ] x ≈ y}{q : [ Γ ] y ≈ x}
              {a : ∣ fm x ∣}{b : ∣ fm y ∣} → 
              [ fm x ] a ≈ substT q b → [ fm y ] substT p a ≈ b
  subst-mir1 eq = [ fm _ ]trans (subst* _ eq) trans-refl

  subst-mir2 : ∀{x y : ∣ Γ ∣}
              {p : [ Γ ] x ≈ y}{q : [ Γ ] y ≈ x}
              {a : ∣ fm x ∣}{b : ∣ fm y ∣} → 
              [ fm y ] substT p a ≈ b → [ fm x ] a ≈ substT q b
  subst-mir2 eq = [ fm _ ]sym (subst-mir1 ([ fm _ ]sym eq))

open Ty public 
  renaming (substT to [_]subst; subst* to [_]subst*; fm to [_]fm ;
            refl* to [_]refl* ; trans* to [_]trans*; subst-pi to [_]subst-pi ;
            subst-pi' to [_]subst-pi' ; subst-pi* to [_]subst-pi* ;
            trans-refl to [_]trans-refl ; subst-mir1 to [_]subst-mir1 ;
            subst-mir2 to [_]subst-mir2)

-- Type substitution


_[_] : ∀ {Γ Δ : Con} → Ty Δ → Γ ⇉ Δ → Ty Γ
_[_] {Γ} {Δ} A f
     = record
     { fm     = fm ∘ fn
     ; substT = substT ∘ resp
     ; subst* = subst* ∘ resp
     ; refl*  = λ _ _ → subst-pi'
     ; trans* = λ p q a → 
                [ fm (fn _) ]trans (trans* _ _ _) subst-pi
     }
     where 
       open Ty A
       open _⇉_ f

record Tm {Γ : Con}(A : Ty Γ) : Set where
  constructor tm:_resp:_
  field
    tm    : (x : ∣ Γ ∣) → ∣ [ A ]fm x ∣
    respt : ∀ {x y : ∣ Γ ∣} → 
              (p : [ Γ ] x ≈ y) → 
              [ [ A ]fm y ] [ A ]subst p (tm x) ≈ tm y

open Tm public renaming (tm to [_]tm ; respt to [_]respt)

-- Term substitution

_[_]m : ∀ {Γ Δ : Con}{A : Ty Δ} → Tm A → (f : Γ ⇉ Δ) → Tm (A [ f ])
_[_]m t f = record 
          { tm = [ t ]tm ∘ [ f ]fn
          ; respt = [ t ]respt ∘ [ f ]resp 
          }

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

uniqueHom : ∀ (Δ : Con) → (f : Δ ⇉ ●) → f ≡ ⋆
uniqueHom Δ f = PE.refl


-- Context Comprehension
 
-- To implement & using &' is because I found Agda does not support lambda pattern matching for implicit arguments (though I found a patch on the Internet) 

_&'_ : (Γ : Con) → Ty Γ → HSetoid'
Γ &' A = record 
       { Carrier = Σ[ x ∶ ∣ Γ ∣ ] ∣ fm x ∣
       ; _≈h_  = λ{(x , a) (y , b) → 
                 Σ'[ p ∶ x ≈h y ] [ fm y ] substT p a ≈h b}
       ; refl  = λ {(a , b) → refl , refl* _ _}
       ; sym   = λ {(_ , a) _ (p , q) → 
                 sym p , 
                 [ fm _ ]trans (subst* _ ([ fm _ ]sym q)) trans-refl } 
       ; trans = λ {_ _ _ (p , q) (m , n) →
                 trans p m , 
                 [ fm _ ]trans ([ fm _ ]trans ([ fm _ ]sym (trans* _ _ _)) (subst* _ q)) n }
       }
       where 
         open HSetoid Γ
         open Ty A     

_&_ : (Γ : Con) → Ty Γ → Con
Γ & A = transVariant (Γ &' A)

infixl 5 _&_

fst& : {Γ : Con}{A : Ty Γ} → Γ & A ⇉ Γ
fst& = record 
         { fn = proj₁
         ; resp = proj₁
         }

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
  { fm = λ x → let Ax = [ A ]fm x in
               let Bx = λ a → [ B ]fm (x , a) in
         record
         { Carrier = Σ[ fn ∶ ((a : ∣ Ax ∣) → ∣ Bx a ∣) ]
                     ((a b : ∣ Ax ∣)
                     (p : [ Ax ] a ≈ b) →
                     [ Bx b ] [ B ]subst ([ Γ ]refl , [ Ax ]trans ([ A ]refl* x a) p) (fn a) ≈ fn b) 
 
     -- f-resp on the paper ignores refl*

         ; _≈h_    = λ{(f , _) (g , _) → ∀'[ a ∶ _ ] [ Bx a ] f a ≈h g a }
         ; refl    = λ a → [ Bx a ]refl 
         ; sym     = λ f a → [ Bx a ]sym (f a)
         ; trans   = λ f g a → [ Bx a ]trans (f a) (g a)
         }

  ; substT = λ {x} {y} p → let y2x = λ a → [ A ]subst ([ Γ ]sym p) a in
                           let x2y = λ a → [ A ]subst p a in
                           let p' = λ a → [ A ]trans-refl in -- p' is different on the paper
             λ{(f , rsp) →  
               (λ a → [ B ]subst (p , p' a) (f (y2x a)))                         
               -- this is g -- g a = [ B ]subst (p , p' a) (f (y2x a))
               ,                                 
               (λ a b q → 
                let a' = y2x a in 
                let b' = y2x b in
                let q' = [ A ]subst* ([ Γ ]sym p) q in
                let H = rsp a' b' q' in
                let r : [ Γ & A ] (x , b') ≈ (y , b)
                    r = (p , p' b) in
                let pre = [ B ]subst* r H in
                
                [ [ B ]fm (y , b) ]trans 
                ([ B ]trans* _ _ _)                 
                ([ [ B ]fm (y , b) ]trans 
                [ B ]subst-pi 
                ([ [ B ]fm (y , b) ]trans 
                ([ [ B ]fm (y , b) ]sym ([ B ]trans* _ _ _)) 
                pre))  
                )
 -- this is g-resp                    
             }


  ; subst* = λ _ q _ → [ B ]subst* _ (q _)
  ; refl* = λ {x (f , rsp) a →  [ [ B ]fm _ ]trans [ B ]subst-pi (rsp ([ A ]subst ([ Γ ]sym [ Γ ]refl) a) a [ A ]subst-pi')  }
  ; trans* = λ p q → λ {(f , rsp) a →
             [ [ B ]fm _ ]trans 
             ([ [ B ]fm _ ]trans 
             ([ B ]trans* _ _ _) 
             ([ [ B ]fm _ ]sym ([ [ B ]fm _ ]trans ([ B ]trans* _ _ _) [ B ]subst-pi))) 
             ([ B ]subst* _ (rsp _ _ ([ [ A ]fm _ ]trans ([ A ]trans* _ _ _) [ A ]subst-pi))) } 
  }

lam : {Γ : Con}{A : Ty Γ}{B : Ty (Γ & A)} → Tm B → Tm (Π A B)
lam {Γ} {A} (tm: tm resp: respt) = 
  record { tm = λ x → (λ a → tm (x , a)) , (λ a b p → respt ([ Γ ]refl , [ [ A ]fm x ]trans ([ A ]refl* _ _) p))
         ; respt = λ p _ → respt (p , [ A ]trans-refl) 
         }

app : {Γ : Con}{A : Ty Γ}{B : Ty (Γ & A)} → Tm (Π A B) → Tm B
app {Γ} {A} {B} (tm: tm resp: respt) = 
  record { tm = λ {(x , a) → proj₁ (tm x) a}
         ; respt = λ {x} {y} → λ {(p , tr) → 
                 let fresp = proj₂ (tm (proj₁ x)) in
                 [ [ B ]fm _ ]trans 
                 ([ B ]subst* (p , tr) ([ [ B ]fm _ ]sym [ B ]subst-pi')) 
                 ([ [ B ]fm _ ]trans
                 ([ B ]trans* ([ Γ ]refl , [ A ]refl* _ _) _ _) 
                 ([ [ B ]fm _ ]trans 
                 [ B ]subst-pi 
                 ([ [ B ]fm _ ]trans 
                 ([ [ B ]fm _ ]sym ([ B ]trans* _ (p , [ A ]trans-refl) _))
                 ([ [ B ]fm _ ]trans 
                 ([ B ]subst-pi* (fresp _ _ ([ A ]subst-mir2 tr))) 
                 (respt p _))))) }
         }

-- to do : verification of β and η


_⇨_ : {Γ : Con}(A B : Ty Γ) → Ty Γ
A ⇨ B = Π A (B [ fst& {A = A} ])

-- simpler definition

[_,_]_⇨fm_ : (Γ : Con)(x : ∣ Γ ∣) → HSetoid → HSetoid → HSetoid
[ Γ , x ] Ax ⇨fm Bx 
  = record
      { Carrier = Σ[ fn ∶ (∣ Ax ∣ → ∣ Bx ∣) ] ((a b : ∣ Ax ∣)(p : [ Ax ] a ≈ b) → [ Bx ] fn a ≈ fn b)
      ; _≈h_    = λ{(f , _) (g , _) → ∀'[ a ∶ _ ] [ Bx ] f a ≈h g a }
      ; refl    = λ _ → [ Bx ]refl 
      ; sym     = λ f a → [ Bx ]sym (f a)
      ; trans   = λ f g a → [ Bx ]trans (f a) (g a)
      }

-- other types are in different files


-- to do: verification

-- verification of functor laws (do we have extensional equality for record types? or eta equality?)
-- define equality with respect to propositions which are proof irrelevant

module TypeTerm-Equality
  (Ty-ExtEq : {Γ : Con}{A B : Ty Γ} →
              (p : [ A ]fm ≡ [ B ]fm) →
              (∀{x}{y}(xy : [ Γ ] x ≈ y)(fx : ∣ [ A ]fm x ∣) → subst (λ fm → ∣ fm y ∣) p ([ A ]subst xy fx) ≡ [ B ]subst xy (subst (λ fm → ∣ fm x ∣) p fx)) →
           A ≡ B)
  (Tm-ExtEq : {Γ : Con}{A : Ty Γ}{t r : Tm A} →
              ([ t ]tm ≡ [ r ]tm) →
              t ≡ r) where

  Fid : {Γ : Con}{A : Ty Γ} → A [ idCH ] ≡ A
  Fid = Ty-ExtEq PE.refl (λ xy fx → PE.refl)

  Fcomp : {Γ Δ Φ : Con}{A : Ty Γ}(f : Δ ⇉ Γ)(g : Φ ⇉ Δ) → A [ f ∘c g ] ≡ A [ f ] [ g ]
  Fcomp f g = Ty-ExtEq PE.refl (λ xy fx → PE.refl) 


  Tm-ExtEq-TyDif : {Γ : Con}{A B : Ty Γ}{t : Tm A}{r : Tm B} → (eq : A ≡ B) → 
                   (∀ x → subst (λ ty → ∣ [ ty ]fm x ∣) eq ([ t ]tm x) ≡ [ r ]tm x) → 
                   (subst Tm eq t ≡ r)
  Tm-ExtEq-TyDif PE.refl f = Tm-ExtEq (ext f)

{-
  Fidm : {Γ : Con}{A : Ty Γ}(t : Tm A) → (subst Tm Fid (t [ idCH ]m)) ≡ t
  Fidm t with Fid
  ... | rere = ? -- Tm-ExtEq-TyDif Fid (λ x → {!trans!})

  Fcompm : {Γ Δ Φ : Con}{A : Ty Γ}{t : Tm A}(f : Δ ⇉ Γ)(g : Φ ⇉ Δ) → subst Tm (Fcomp f g) (t [ f ∘c g ]m) ≡ t [ f ]m [ g ]m
  Fcompm f g = {!!} 
 
-- verify Π types are consistent with substitution

  Pi-Sub : {Γ Δ : Con}(A : Ty Γ)(B : Ty (Γ & A))(f : Δ ⇉ Γ) →
          (Π A B) [ f ] ≡ Π (A [ f ]) (B [ f ^ A ])
  Pi-Sub A B f = Ty-ExtEq {!ext!} {!!}

-}