\AgdaHide{
\begin{code}

{-# OPTIONS --type-in-type #-}

import Level
open import Relation.Binary.PropositionalEquality as PE hiding (refl ; sym ; trans; isEquivalence; [_])

module CwF-ctd (ext : Extensionality Level.zero Level.zero) where

open import Data.Unit
open import Function
open import Data.Product

open import CwF-setoidwo ext public

open import Data.Nat

\end{code}
}

Binary relation

\begin{code}

Rel : {Γ : Con} → Ty Γ → Set₁
Rel {Γ} A = Ty (Γ & A & A [ fst& {A = A} ]T)

\end{code}

Natural numbers

\begin{code}

module Natural (Γ : Con) where

  _≈nat_ : ℕ → ℕ → HProp
  zero ≈nat zero = ⊤'
  zero ≈nat suc n = ⊥'
  suc m ≈nat zero = ⊥'
  suc m ≈nat suc n = m ≈nat n
  
  reflNat : {x : ℕ} → < x ≈nat x > 
  reflNat {zero} = tt
  reflNat {suc n} = reflNat {n}

  symNat : {x y : ℕ} → < x ≈nat y > → < y ≈nat x >
  symNat {zero} {zero} eq = tt
  symNat {zero} {suc _} eq = eq
  symNat {suc _} {zero} eq = eq
  symNat {suc x} {suc y} eq = symNat {x} {y} eq

  transNat : {x y z : ℕ} → < x ≈nat y > → < y ≈nat z > → < x ≈nat z >
  transNat {zero} {zero} xy yz = yz
  transNat {zero} {suc _} () yz
  transNat {suc _} {zero} () yz
  transNat {suc _} {suc _} {zero} xy yz = yz
  transNat {suc x} {suc y} {suc z} xy yz = transNat {x} {y} {z} xy yz

  ⟦Nat⟧ : Ty Γ
  ⟦Nat⟧ = record 
    { fm = λ γ → record
         { Carrier = ℕ
         ; _≈h_ = _≈nat_
         ; refl = λ {n} → reflNat {n}
         ; sym = λ {x} {y} → symNat {x} {y}
         ; trans = λ {x} {y} {z} → transNat {x} {y} {z}
         }
    ; substT = λ _ → id
    ; subst* = λ _ → id
    ; refl* = λ x a → reflNat {a}
    ; trans* = λ a → reflNat {a} 
    }

  ⟦0⟧ : Tm ⟦Nat⟧
  ⟦0⟧ = record
      { tm = λ _ → 0
      ; respt = λ p → tt
      }

  ⟦s⟧ : Tm ⟦Nat⟧ → Tm ⟦Nat⟧
  ⟦s⟧ (tm: t resp: respt) 
      = record
      { tm = suc ∘ t
      ; respt = respt
      }

\end{code}

Simply typed universe

\AgdaHide{
\begin{code}

{-
  data  ⟦U⟧⁰ : Set where
    nat : ⟦U⟧⁰
    arr<_,_> : (a b : ⟦U⟧⁰) → ⟦U⟧⁰

  _~⟦U⟧_ : ⟦U⟧⁰ → ⟦U⟧⁰ → HProp
  nat ~⟦U⟧ nat = ⊤'
  nat ~⟦U⟧ arr< a , b > = ⊥'
  arr< a , b > ~⟦U⟧ nat = ⊥'
  arr< a , b > ~⟦U⟧ arr< a' , b' > = a ~⟦U⟧ a' ∧ b ~⟦U⟧ b'

  reflU :  {x : ⟦U⟧⁰} → < x ~⟦U⟧ x >
  reflU {nat} = tt
  reflU {arr< a , b >} = reflU {a} , reflU {b}

  symU : {x y : ⟦U⟧⁰} → < x ~⟦U⟧ y > → < y ~⟦U⟧ x >
  symU {nat} {nat} eq = tt
  symU {nat} {arr< a , b >} eq = eq
  symU {arr< a , b >} {nat} eq = eq
  symU {arr< a , b >} {arr< a' , b' >} (p , q) = (symU {a} {a'} p) 
                                               , (symU {b} {b'} q)

  transU : {x y z : ⟦U⟧⁰} → < x ~⟦U⟧ y > → < y ~⟦U⟧ z > → < x ~⟦U⟧ z >
  transU {nat} {nat} eq1 eq2 = eq2
  transU {nat} {arr< a , b >} () eq2
  transU {arr< a , b >} {nat} () eq2
  transU {arr< a , b >} {arr< a' , b' >} {nat} eq1 eq2 = eq2
  transU {arr< a , b >} {arr< a' , b' >} {arr< a0 , b0 >} (p1 , q1) 
         (p2 , q2) = (transU {a} {a'} {a0} p1 p2) 
         , transU {b} {b'} {b0} q1 q2

  ⟦U⟧ : Ty Γ
  ⟦U⟧ = record 
    { fm = λ γ → record
         { Carrier = ⟦U⟧⁰
         ; _≈h_ = _~⟦U⟧_
         ; refl = λ {x} → reflU {x}
         ; sym = λ {x} {y} → symU {x} {y}
         ; trans = λ {x} {y} {z} → transU {x} {y} {z}
         }
    ; substT = λ _ → id
    ; subst* = λ _ → id
    ; refl* = λ x a → reflU {a}
    ; trans* = λ a → reflU {a}
    }

  elfm : Σ ∣ Γ ∣ (λ x → ⟦U⟧⁰) → HSetoid
  elfm (γ , nat) = [ ⟦Nat⟧ ]fm γ
  elfm (γ , arr< a , b >) = [ Γ , γ ] elfm (γ , a) ⇒fm elfm (γ , b)
-}

\end{code}
}

\AgdaHide{
\begin{code}

{- To do : To find the way to extract the substT from ->

  elsubstT : {x y : Σ ∣ Γ ∣ (λ x' → ⟦U⟧⁰)} →
      Σ < [ Γ ] proj₁ x ≈h proj₁ y > (λ x' → < proj₂ x ~⟦U⟧ proj₂ y >) →
      ∣ elfm x ∣ → ∣ elfm y ∣
  elsubstT {_ , nat} {_ , nat} _ x' = x'
  elsubstT {_ , nat} {_ , arr< a , b >} (p , ()) x'
  elsubstT {_ , arr< a , b >} {_ , nat} (p , ()) x'
  elsubstT {γ , arr< a , b >} {γ' , arr< a' , b' >} (p , qa , qb) (s1 , s2) = 
   {!!}

  ⟦El⟧ : Ty (Γ & ⟦U⟧)
  ⟦El⟧ = record 
       { fm = elfm
       ; substT = elsubstT
       ; subst* = {!!}
       ; refl* = {!!}
       ; trans* = {!!} 
       }

-}
\end{code}
}

The equality type

\begin{code}

module Equality-Type (Γ : Con)(A : Ty Γ) where

  ⟦Id⟧ : Rel A
  ⟦Id⟧ = record 
    { fm = λ {((x , a) , b) → 
             record 
             { Carrier = [ [ A ]fm x ] a ≈ b
             ; _≈h_ = λ _ _ → record { prf = ⊤ ; Uni = PE.refl }
             ; refl = tt 
             ; sym = id
             ; trans = λ _ _ → tt
             }
             }
    ; substT = λ {((x , a) , b) x0 → 
               [ [ A ]fm _ ]trans 
               ([ [ A ]fm _ ]sym a) 
               ([ [ A ]fm _ ]trans 
               ([ A ]subst* _ x0) b) 
               }
    ; subst* = λ _ _ → tt
    ; refl* = λ _ _ → tt
    ; trans* = λ _ → tt 
    }


  ⟦refl⟧⁰ : Tm {Γ & A} (⟦Id⟧ [ record { fn = λ x' → x' , proj₂ x' 
                       ; resp = λ x' → x' , proj₂ x' } ]T) 
  ⟦refl⟧⁰ = record
           { tm = λ {(x , a) → [ [ A ]fm x ]refl {a} }
           ; respt = λ p → tt
           }

  ⟦refl⟧ =  lam {Γ} {A} ⟦refl⟧⁰

\end{code}

Subst using equality types

\begin{code}

  module substIn (B : Ty (Γ & A)) where
  
    ⟦subst⟧⁰ : Tm {Γ & A & (A [ fst& {A = A} ]T) 
               & ⟦Id⟧ & B [ fst& {A = A [ fst& {A = A} ]T}  ]T 
               [ fst& {A = ⟦Id⟧} ]T} 
             (B [ record { fn = λ x → (proj₁ (proj₁ (proj₁ (proj₁ x)))) 
             , (proj₂ (proj₁ (proj₁ x))) 
             ; resp = λ x → proj₁ (proj₁ (proj₁ (proj₁ x))) 
             , proj₂ (proj₁ (proj₁ x)) } ]T)

    ⟦subst⟧⁰ = record
           { tm = λ {((((x , a) , b) , p) , PA) → [ B ]subst 
                  ([ Γ ]refl , [ [ A ]fm _ ]trans 
                  ([ A ]refl* _ _) p) PA }
           ; respt = λ {((((m , a) , b) , p) , PA) → 
             [ [ B ]fm _ ]trans 
             ([ B ]trans* _) 
              ([ [ B ]fm _ ]trans 
             [ B ]subst-pi 
             ([ [ B ]fm _ ]trans 
             ([ [ B ]fm _ ]sym ([ B ]trans* _))
             ([ B ]subst* _ PA) )) }
           }
\end{code}


\AgdaHide{
\begin{code}

--    ⟦subst⟧ = lam (lam (lam ⟦subst⟧⁰))
    
\end{code}
}