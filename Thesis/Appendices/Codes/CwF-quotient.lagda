
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
      ; sym     = λ {(a , b) → (b , a)}
      ; trans   = λ {(a , b) (a' , b') 
                  → (a' ∘ a) , (b ∘ b')}
      }

⟦Prop⟧ : {Γ : Con} → Ty Γ
⟦Prop⟧ = record 
          { fm = λ x → Pu
          ; substT = λ _ x → x
          ; subst* = λ p x → x
          ; refl* = λ x a → id , id
          ; trans* = λ _ → id , id }

\end{code}
\AgdaHide{
\begin{code}

{-
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
-}

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
PropRel : {Γ : Con}(A : Ty Γ)(γ : ∣ Γ ∣) → Set
PropRel {Γ} A γ = ∣ [ A ]fm γ ∣ → ∣ [ A ]fm γ ∣ → HProp
\end{code}

Quotient types

\begin{code}
module Q (Γ : Con)(A : Ty Γ)
         (R : (γ : ∣ Γ ∣) → PropRel A γ)
         (Rrsp : ∀ {γ a b} → [ [ A ]fm γ ] a ≈ b → < R γ a b >)
         (Rref : ∀ {γ a} → < R γ a a >)
         (Rsym : (∀ {γ a b} → < R γ a b > → < R γ b a >))
         (Rtrn :  (∀ {γ a b c} → < R γ a b > 
                 →  < R γ b c > → < R γ a c >))
         (Rsubst : ∀{γ γ' : ∣ Γ ∣} 
                   (x y : ∣ [ A ]fm γ ∣)
                   (p : [ Γ ] γ ≈ γ') →
                   < R γ x y > → 
                   < R γ' ([ A ]subst p x) ([ A ]subst p y) >)
         where

  ⟦Q⟧₀ : ∣ Γ ∣ → HSetoid
  ⟦Q⟧₀ γ = record
         { Carrier = ∣ [ A ]fm γ ∣
         ; _≈h_ = R γ
         ; refl = Rref
         ; sym = Rsym
         ; trans = Rtrn
         }


  ⟦Q⟧ : Ty Γ
  ⟦Q⟧ = record 
    { fm = ⟦Q⟧₀
    ; substT = [ A ]subst
    ; subst* = λ p q → Rsubst _ _ p q
    ; refl* = λ γ a → Rrsp ([ A ]refl* _ _)
    ; trans* = λ a → Rrsp ([ A ]trans* _)
    }

  ⟦[_]⟧ : Tm A → Tm ⟦Q⟧
  ⟦[ x ]⟧ = record
           { tm = [ x ]tm
           ; respt = λ p → Rrsp ([ x ]respt p)
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


{-




{-
       data RC
              : A → A → Set where
     emb : ∀{a b} → R a b → Closure' R a b
     rfl : ∀{a b} → [ [ A ]fm γ ] a ≈ b → Closure' R a b
     cls : ∀{a b c} → R b a → Closure' {A} {_≈_} R b c 
         → Closure' R a c

sym : ∀{A}{_≈_ : A → A → Set}{R : A → A → Set}
    →  ∀ {a b} → Closure' {A} {_≈_} R a b → Closure' {A} {_≈_} R b a
sym (emb x) = cls x {!!}
sym (rfl x) = {!!}
sym (cls x ab) = {!!}

trn : ∀{A}{_≈_ : A → A → Set}{R : A → A → Set}
    →  ∀ {a b c} → Closure' {A} {_≈_} R a b → Closure' {A} {_≈_} R b c
    → Closure' {A} {_≈_} R a c
trn (emb x) bc = {!cls x bc!}
trn (rfl x) bc = {!!}
trn (cls x ab) bc = {!!} -- cls {!ab!} bc
-}


{-
  data RC₀ (γ : ∣ Γ ∣) : ∣ [ A ]fm γ ∣ → ∣ [ A ]fm γ ∣ → Set where
     emb : ∀{a b} → < R γ a b > → RC₀ γ a b
     ref : ∀{a b} → [ [ A ]fm γ ] a ≈ b → RC₀ γ a b
     cls : ∀{a b c} → < R γ b a > → RC₀ γ b c
         → RC₀ γ a c

  sym : ∀{γ a b} → RC₀ γ a b → RC₀ γ b a
  sym (emb x) = cls x (ref [ [ A ]fm _ ]refl)
  sym (ref x) = ref ([ [ A ]fm _ ]sym x)
  sym (cls x bc) = {!bc!} -- cls {!bc!} (emb x)


  trn : ∀ {γ a b c} → RC₀ γ a b → RC₀ γ b c
      → RC₀ γ a c
  trn (emb x) bc =  cls {!x!} bc
  trn (ref x) bc = {!!}
  trn (cls x ab) bc = {!!} -- cls {!ab!} bc
-}




  data RC₀ (γ : ∣ Γ ∣) : ∣ [ A ]fm γ ∣ → ∣ [ A ]fm γ ∣ → Set where
     emb : ∀{a b} → < R γ a b > → RC₀ γ a b
     ref : ∀{a b} → [ [ A ]fm γ ] a ≈ b → RC₀ γ a b
     trn : ∀{a b c} → RC₀ γ a b → RC₀ γ b c
           → RC₀ γ a c
     sym : ∀{a b} → RC₀ γ a b → RC₀ γ b a


  RC' : (γ : ∣ Γ ∣) → (a b : ∣ [ A ]fm γ ∣)
      → (p q : RC₀ γ a b) → p ≡ q
  RC' γ a b = {!!}

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
         ; _≈h_ = R γ -- RC γ
         ; refl = Rref -- λ {x} _ _ _ x₃ _ → x₃ x x [ [ A ]fm γ ]refl
         ; sym = Rsym -- λ {x} {y} x≈y R' x₁ x₂ x₃ x₄ → x₁ _ _ (x≈y R' x₁ x₂ x₃ x₄)
         ; trans = Rtrn --λ {x} {y} {z} x≈y y≈z R' x₁ x₂ x₃ x₄ 
                   -- → x₂ _ _ _ (x≈y R' x₁ x₂ x₃ x₄) (y≈z R' x₁ x₂ x₃ x₄)
         }


  ⟦Q⟧ : Ty Γ
  ⟦Q⟧ = record 
    { fm = ⟦Q⟧₀
    ; substT = [ A ]subst
    ; subst* = λ p q → Rsubst _ _ p q --Rresp ([ A ]subst-pi* {!!})  λ p → RC-subst _ _ p
    ; refl* = λ γ a → Rresp ([ A ]refl* _ _) --λ x a R' x₁ x₂ x₃ x₄ → x₃ _ _ ([ A ]refl* _ _)
    ; trans* = λ a → Rresp ([ A ]trans* _) -- λ a R' x₁ x₂ x₃ x₄ → x₃ _ _ ([ A ]trans* _)
    }

  ⟦[_]⟧ : Tm A → Tm ⟦Q⟧
  ⟦[ x ]⟧ = record
           { tm = [ x ]tm
           ; respt = {!!} -- λ p R' _ _ x₄ _ → x₄ _ _ ([ x ]respt p)
           }



-}





{-
Closure' : (A : Set)(_∼_ R : A → A → HProp) → A → A → HProp
Closure' A _∼_ R s s'
          = ∀' (A → A → HProp) (λ R' 
          → ∀'[ x ∶ A ] ∀'[ y ∶ A ] R' x y ⇛ R' y x
            ⇛ (∀'[ x ∶ A ] ∀'[ y ∶ A ] ∀'[ z ∶ A ] R' x y ⇛ 
              R' y z ⇛ R' x z)
            ⇛ (∀'[ x ∶ A ] ∀'[ y ∶ A ] x ∼ y ⇛ R' x y)
            ⇛ (∀'[ x ∶ A ] ∀'[ y ∶ A ] R x y ⇛ R' x y)
            ⇛ R' s s')
-}


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


-- Rel≈ : 

--        (R≈ : ∀ {γ : ∣ Γ ∣}{r1 r2 : PropRel A γ}
--               {a b :  ∣ [ A ]fm γ ∣} → ∀ a b → < r1 a b ⇄ r2 a b >)
{-
Eqv₀ : {Γ : Con}(A : Ty Γ) → ∣ Γ ∣ → HSetoid
Eqv₀ {Γ} A γ = record
         { Carrier = ∣ [ A ]fm γ ∣ → ∣ [ A ]fm γ ∣ → HProp
         ; _≈h_ = λ r1 r2 → ∀' _ (λ a → ∀' _ (λ b → r1 a b ⇄ r2 a b))
         ; refl = λ _ _ → (λ x → x) , (λ x → x)
         ; sym = λ eq a b → let (p , q) = eq a b in q , p
         ; trans = λ eq1 eq2 a b →
                     let (p1 , q1) = eq1 a b in 
                     let (p2 , q2) = eq2 a b in
                     (p2 ∘ p1) , (q1 ∘ q2)
         }
-}

{-
Eqv : {Γ : Con}(A : Ty Γ) → Ty Γ
Eqv {Γ} A =  record
    { fm = Eqv₀ A
    ; substT = λ p r1 → λ a b 
               → r1 ([ A ]subst ([ Γ ]sym p) a)
               ([ A ]subst ([ Γ ]sym p) b)
    ; subst* = λ {γ} {γ'} p {R1} {R2} eq → λ a b → {!!} {-
λ p {R1} {R2} eq a b → eq ([ A ]subst ([ Γ ]sym p) a) 
               ([ A ]subst ([ Γ ]sym p) b)
-}
    ; refl* = λ γ R → λ a b → {!!}
    ; trans* = {!!}
    }

-}


-- Rsubst' = subst-pi*




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




\AgdaHide{
\begin{code}
{-
BRel : {Γ : Con}(A : Ty Γ) → Ty Γ
BRel A = A ⇒ A ⇒ ⟦Prop⟧


Tm {Γ , A , A [ fst& {A = A} ]} ⟦Prop⟧

record Equiv {Γ : Con}(A : Ty Γ) : Set where
  field
    R : Tm (BRel A)
    ref : Tm (Π A ((BRel A) [ record { fn = λ x → {!x!} 
                       ; resp = {!!}} ]T))



BRel-set : {Γ : Con}{A : Ty Γ} → Tm (BRel A) 
   → (γ : ∣ Γ ∣) → ∣ [ A ]fm γ ∣ →  ∣ [ A ]fm γ ∣ → HProp
BRel-set R γ m n = proj₁ (proj₁ ([ R ]tm γ) m) n
-}
\end{code}
}