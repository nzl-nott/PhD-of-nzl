\begin{code}

module CoSetoid where


open import Relation.Binary.PropositionalEquality as PE hiding ([_] ; refl; sym ; trans; isEquivalence)
open import Function
open import Data.Product
open import Level

record Subset {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    prj₁ : A
    .prj₂ : B prj₁
open Subset

record Setoid : Set₁ where
  infix 4 _≈_
  field
    Carrier : Set
    _≈_     : Carrier → Carrier → Set
    .refl   : ∀{x} → x ≈ x
    .sym    : ∀{x y} → x ≈ y → y ≈ x
    .trans  : ∀{x y z} → x ≈ y → y ≈ z → x ≈ z
open Setoid renaming 
     (Carrier to ∣_∣ ; _≈_ to [_]_≈_ ; refl to [_]refl; trans to [_]trans; sym to [_]sym)


infix 5 _⇉_

record _⇉_ (A B : Setoid) : Set where
  constructor fn:_resp:_
  field
    fn   : ∣ A ∣ → ∣ B ∣
    .resp : {x y : ∣ A ∣} → 
           .([ A ] x ≈ y) → 
           [ B ] fn x ≈ fn y
open _⇉_ public renaming (fn to [_]fn ; resp to [_]resp)


record Ty (Γ : Setoid) : Set₁ where
  field
    fm     : ∣ Γ ∣ → Setoid -- the setoid of types associated to Context Γ

-- substT p is the homomorphism between setoid of types, substitution of terms

    substT : {x y : ∣ Γ ∣} → 
             .([ Γ ] x ≈ y) →
             ∣ fm x ∣ → 
             ∣ fm y ∣
    .subst* : ∀{x y : ∣ Γ ∣}  -- substT respects the equality
             (p : ([ Γ ] x ≈ y))
             {a b : ∣ fm x ∣} →
             .([ fm x ] a ≈ b) →
             [ fm y ] substT p a ≈ substT p b

-- beta equality (Computation rules)

    .refl*  : ∀{x : ∣ Γ ∣}{a : ∣ fm x ∣} → 
             [ fm x ] substT ([ Γ ]refl) a ≈ a
    .trans* : ∀{x y z : ∣ Γ ∣}
             {p : [ Γ ] x ≈ y}
             {q : [ Γ ] y ≈ z}
             (a : ∣ fm x ∣) → 
             [ fm z ] substT q (substT p a) ≈ substT ([ Γ ]trans p q) a

  .tr* : ∀{x y : ∣ Γ ∣}
          {p : [ Γ ] y ≈ x}
          {q : [ Γ ] x ≈ y}
          {a : ∣ fm x ∣} → 
          [ fm x ] substT p (substT q a) ≈ a
  tr* = [ fm _ ]trans (trans* _) refl*

  substT-inv : {x y : ∣ Γ ∣} → 
             .([ Γ ] x ≈ y) →
             ∣ fm y ∣ → 
             ∣ fm x ∣
  substT-inv p y = substT ([ Γ ]sym p) y

open Ty public 
  renaming (substT to [_]subst; substT-inv to [_]subst-inv; subst* to [_]subst*; fm to [_]fm ;
            refl* to [_]refl* ; trans* to [_]trans*; tr* to [_]tr*)


_[_]T : ∀ {Γ Δ : Setoid} → Ty Δ → Γ ⇉ Δ → Ty Γ
_[_]T {Γ} {Δ} A f
     = record
     { fm     = λ x → fm (fn x)
     ; substT = λ p → substT _
     ; subst* = λ p → subst* (resp p)
     ; refl*  = refl*
     ; trans* = trans*
     }
     where 
       open Ty A
       open _⇉_ f
  

_&_ : (Γ : Setoid) → Ty Γ → Setoid
Γ & A = record { Carrier = Σ[ x ∶ ∣ Γ ∣ ] ∣ fm x ∣ 
               ; _≈_ = λ{(x , a) (y , b) → Σ[ p ∶ x ≈ y ] [ fm y ] (substT p a) ≈ b }
               ; refl = refl , refl*
               ; sym =  λ {(p , q) → (sym p) , [ fm _ ]trans (subst* _ ([ fm _ ]sym q)) tr* }
               ; trans = λ {(p , q) (m , n) → trans p m , [ fm _ ]trans ([ fm _ ]trans ([ fm _ ]sym (trans* _)) (subst* _ q)) n}
               }
    where
      open Setoid Γ
      open Ty A



Π : {Γ : Setoid}(A : Ty Γ)(B : Ty (Γ & A)) → Ty Γ
Π {Γ} A B = record 
  { fm = λ x → let Ax = [ A ]fm x in
               let Bx = λ a → [ B ]fm (x , a) in
         record
         { Carrier = Subset ((a : ∣ Ax ∣) → ∣ Bx a ∣) (λ fn → 
                     (a b : ∣ Ax ∣)
                     (p : [ Ax ] a ≈ b) →
                     [ Bx b ] [ B ]subst ([ Γ ]refl , [ Ax ]trans [ A ]refl* p) (fn a) ≈ fn b)


         ; _≈_    = λ{(f , _) (g , _) → ∀ a → [ Bx a ] f a ≈ g a } -- {!!} }
         ; refl    = λ a → [ Bx _ ]refl 
         ; sym     = λ f a → [ Bx _ ]sym (f a)
         ; trans   = λ f g a → [ Bx _ ]trans (f a) (g a)
         }

  ; substT = λ {x} {y} p → λ {(f , rsp) →
                   let y2x = λ a → [ A ]subst ([ Γ ]sym p) a in
                   let x2y = λ a → [ A ]subst p a in
             (λ a → [ B ]subst (p , [ A ]tr*) 
             (f (y2x a))) , 
             (λ a b q →
                let a' = y2x a in 
                let b' = y2x b in
                let q' = [ A ]subst* ([ Γ ]sym p) q in
                let H = rsp a' b' ([ A ]subst* ([ Γ ]sym p) q) in
                let r : [ Γ & A ] (x , b') ≈ (y , b)
                    r = (p , [ A ]tr*) in
                let pre = [ B ]subst* r (rsp a' b' ([ A ]subst* ([ Γ ]sym p) q)) in 
                [ [ B ]fm (y , b) ]trans 
                ([ B ]trans* _) 
                ([ [ B ]fm (y , b) ]trans 
                ([ [ B ]fm (y , b) ]sym ([ B ]trans* _)) 
                pre))}


  ; subst* = λ _ q _ → [ B ]subst* _ (q _)
  ; refl* = λ {x} {a} ax 
          → let rsp = prj₂ a in (rsp _ _ [ A ]refl*)
  ; trans* =  λ {(f , rsp) a →
             [ [ B ]fm _ ]trans 
             ([ [ B ]fm _ ]trans 
             ([ B ]trans* _) 
             ([ [ B ]fm _ ]sym ([ B ]trans* _)))
             ([ B ]subst* _ (rsp _ _ ([ A ]trans* _) )) }


  }

\end{code}