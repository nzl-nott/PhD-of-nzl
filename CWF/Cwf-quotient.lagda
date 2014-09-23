
\AgdaHide{
\begin{code}

{-# OPTIONS --type-in-type #-}

import Level
open import Relation.Binary.PropositionalEquality as PE hiding (refl ; sym ; trans; isEquivalence; [_])

module CwF-quotient (ext : Extensionality Level.zero Level.zero) where

open import Data.Unit
open import Function
open import Data.Product


open import CwF-ctd ext
\end{code}
}

Propositions

\begin{code}

Pu : HSetoid
Pu = record
      { Carrier = HProp
      ; _≈h_    = _⇄_
      ; refl    = id , id 
      ; sym     = λ {(a , b) →(b , a)}
      ; trans   = λ {(a , b) (a' , b') 
                  → (a' ∘ a) , (b ∘ b')}
      }


⟦Prop⟧ : Ty ●
⟦Prop⟧ = record { fm = λ x → Pu; substT = λ x' x0 → x0;
                 subst* = λ p x' → x'; refl* = λ x a → id ,
                           id; trans* = λ _ → id , id }

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

\end{code}

\AgdaHide{
\begin{code}
{-
--Several isomorphisms

isoPi1 : {Γ : Con}{A : Ty Γ}{B : Ty (Γ & A)} → Tm {Γ & A} B → Tm (Π A B)
isoPi1 (tm: tm resp: respt) = tm: (λ x → (λ a → tm (x , a)) , (λ a b p → respt _)) resp: (λ p x' → respt _)



abstract
  PropRel   : {Γ : Con}(A : Ty Γ) → Ty Γ
  PropRel A = Π A (Π (A [ fst& {A = A} ]T) {!!}) -- (⟦Prop⟧ [ fn: (λ x → tt) resp: (λ x' → tt) ]T))
-}

-- postulate apply : {Γ : Con}{A : Ty Γ} → Tm (PropRel A) → Tm A → Tm A → Tm ⟦Prop⟧

-- Refl : {Γ : Con}(A : Ty Γ) → Tm (PropRel A) → Ty Γ
-- Refl A rel =  {!!} -- Π A → {!apply !}

{-Equiv :  {Γ : Con}(A : Ty Γ) → Ty Γ
Equiv A = Σ'' (PropRel A)  {!!}
-}          

{-
stack overflow
Refl : {Γ : Con}(A : Ty Γ) → Tm (PropRel A) → Ty Γ
Refl A rel = ?
-}

-- Eqv : 

-- Rel A
\end{code}
}

Propostional relation

\begin{code}

PropRel   : {Γ : Con}(A : Ty Γ) → Ty Γ
PropRel A = A ⇒ A ⇒ ⟦Prop⟧ [ fn: (λ x → tt) resp: (λ x' → tt) ]T

\end{code}

reflexive, symmetric and transitive closure of $\mathsf{R}$

\begin{code}
Closure' : (A : Set)(_∼_ R : A → A → HProp) → A → A → HProp
Closure' A _∼_ R s s'
          = ∀' (A → A → HProp) (λ R' 
          → ∀'[ x ∶ A ] ∀'[ y ∶ A ] R' x y ⇛ R' y x
            ⇛ (∀'[ x ∶ A ] ∀'[ y ∶ A ] ∀'[ z ∶ A ] R' x y ⇛ 
              R' y z ⇛ R' x z)
            ⇛ (∀'[ x ∶ A ] ∀'[ y ∶ A ] x ∼ y ⇛ R' x y)
            ⇛ (∀'[ x ∶ A ] ∀'[ y ∶ A ] R x y ⇛ R' x y)
            ⇛ R' s s')
\end{code}

Simpler way to define closure

\begin{code}

Closure : (A : Set)(_∼_ R : A → A → HProp) 
         → A → A → HProp
Closure A _∼_ R s s'
          = record
            { prf = ∀ (R' : A → A → HProp) 
                  → (∀ x y → < R' x y > → < R' y x >)
                  → (∀ x y z → < R' x y > → < R' y z > → < R' x z >)
                  → (∀ x y → < x ∼ y > → < R' x y >)
                  → (∀ x y → < R x y > → < R' x y >)
                  → < R' s s' >
            ; Uni = ext (λ R' → ext (λ x₁ → ext 
                    (λ x₂ → ext (λ x₃ → ext (λ x₄ → Uni (R' s s'))))))
            }

\end{code}

\AgdaHide{
\begin{code}
{-
incl : {γ : ∣ Γ ∣}{a b :  ∣ [ A ]fm γ ∣} → < R γ a b > → < RC γ a b >
incl r = λ R' x x₁ x₂ x₃ → x₃ _ _ r
-}

{-         (Rresp :  ∀ {γ : ∣ Γ ∣}
           (x y : ∣ [ A ]fm γ ∣)(x' y' : ∣ [ A ]fm γ ∣)
           (eq2 : < rel ([ A ]fm γ) x x' >)
           (eq3 : < rel ([ A ]fm γ) y y' >) 
           → < R γ x y ⇄ R γ x' y' >)


  Qsubst* : (γ γ' : ∣ Γ ∣)(p : [ Γ ] γ ≈ γ') 
          → (a b :  ∣ [ A ]fm γ ∣) 
          → < RC γ a b > 
          → < RC γ' ([ A ]subst p a) ([ A ]subst p b) >
  Qsubst* γ γ' p a b = {!!}


_ (rel ([ A ]fm γ)) (R γ)
  
  postulate RCresp : ∀{γ γ' : ∣ Γ ∣}{a b :  ∣ [ A ]fm γ ∣}
                      {f : ∣ [ A ]fm γ ∣ → ∣ [ A ]fm γ' ∣}  
                       → (< R γ a b > → < R γ' (f a) (f b) >) 
                        → (< RC γ a b > → < RC γ' (f a) (f b) >)


-}
\end{code}
}

Quotient types

\begin{code}

module Q (Γ : Con)(A : Ty Γ)
         (R : (γ : ∣ Γ ∣) → ∣ [ A ]fm γ ∣ → ∣ [ A ]fm γ ∣ → HProp)
         (R-subst : ∀{γ γ' : ∣ Γ ∣} 
                   (x y : ∣ [ A ]fm γ ∣)
                   (eq1 : [ Γ ] γ ≈ γ') →
                   < R γ x y > → 
                   < R γ' ([ A ]subst eq1 x) ([ A ]subst eq1 y) >)
         where

  RC : (γ : ∣ Γ ∣) → ∣ [ A ]fm γ ∣ → ∣ [ A ]fm γ ∣ → HProp
  RC γ = Closure _ (rel ([ A ]fm γ)) (R γ)
  
  postulate RC-subst : ∀{γ γ' : ∣ Γ ∣} 
                     (x y : ∣ [ A ]fm γ ∣)
                     (eq1 : [ Γ ] γ ≈ γ') →
                     < RC γ x y > → 
                     < RC γ' ([ A ]subst eq1 x) ([ A ]subst eq1 y) >

  ⟦Q⟧₀ : ∣ Γ ∣ → HSetoid
  ⟦Q⟧₀ γ =
         record
         { Carrier = ∣ [ A ]fm γ ∣
         ; _≈h_ = RC γ
         ; refl = λ {x} _ _ _ x₃ _ → x₃ x x [ [ A ]fm γ ]refl
         ; sym = λ {x} {y} x≈y R' x₁ x₂ x₃ x₄ → x₁ _ _ (x≈y R' x₁ x₂ x₃ x₄)
         ; trans = λ {x} {y} {z} x≈y y≈z R' x₁ x₂ x₃ x₄ 
                   → x₂ _ _ _ (x≈y R' x₁ x₂ x₃ x₄) (y≈z R' x₁ x₂ x₃ x₄)
         }


  ⟦Q⟧ : Ty Γ
  ⟦Q⟧ = record 
    { fm = ⟦Q⟧₀
    ; substT = [ A ]subst
    ; subst* = λ p → RC-subst _ _ p
    ; refl* = λ x a R' x₁ x₂ x₃ x₄ → x₃ _ _ ([ A ]refl* _ _)
    ; trans* = λ a R' x₁ x₂ x₃ x₄ → x₃ _ _ ([ A ]trans* _)
    }

  ⟦[_]⟧ : Tm A → Tm ⟦Q⟧
  ⟦[ x ]⟧ = record
           { tm = [ x ]tm
           ; respt = λ p R' _ _ x₄ _ → x₄ _ _ ([ x ]respt p)
           }

\end{code}

\AgdaHide{
\begin{code}
{-
  Q-elim : (B : Ty Γ) 
         → (f : ∀ γ → ∣ [ A ]fm γ ∣ → ∣ [ B ]fm γ ∣)
         → (frespt : ∀ γ γ' a b → (p : [ Γ ] γ ≈ γ')
                  → ([ [ A ]fm γ ] a ≈ b)
                  → [ [ B ]fm γ' ]  [ B ]subst p (f γ a) ≈ f γ' b)
         → (∀ γ a b → < RC γ a b > → [ [ B ]fm γ ] f γ a ≈ f γ b)
         → Tm (⟦Q⟧ ⇒ B)
  Q-elim B f fresp fsubst respR = record
           { tm = λ γ → f γ , (λ a b p → [ [ B ]fm γ ]trans 
                              [ B ]subst-pi' (respR γ a b p))
           ; respt = λ {γ} {γ'} p a → {!fsubst γ γ' p!} -- λ p R' _ _ x₄ _ → x₄ _ _ ([ x ]respt p)
           }

-}



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

\end{code}
}