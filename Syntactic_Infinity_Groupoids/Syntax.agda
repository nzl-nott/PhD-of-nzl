{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check #-}

module Syntax where

open import Relation.Binary.PropositionalEquality
open import Function

-- Type Signatures

data Con : Set
data Ty (Γ : Con) : Set
data Tm : {Γ : Con} (A : Ty Γ) → Set
data Var : {Γ : Con}(A : Ty Γ) → Set
data isContr : Con → Set
data _⇒_ : Con → Con → Set

infix 4 _≅_

-- contravariant
_[_]T  : {Γ Δ : Con}(A : Ty Δ)           (δ : Γ ⇒ Δ) → Ty Γ
_[_]V  : {Γ Δ : Con}{A : Ty Δ}(a : Var A)(δ : Γ ⇒ Δ) → Tm (A [ δ ]T) -- not Var, because can be replaced by JJ
_[_]tm : {Γ Δ : Con}{A : Ty Δ}(a : Tm A) (δ : Γ ⇒ Δ) → Tm (A [ δ ]T)

-- JM equality for Tm

data _≅_ {Γ : Con}{A : Ty Γ}: {B : Ty Γ} → Tm A → Tm B → Set where
  refl : (b : Tm A) → b ≅ b

-- sym

_-¹ : ∀{Γ : Con}{A B : Ty Γ}{a : Tm A}{b : Tm B} → a ≅ b → b ≅ a
(refl _) -¹ = refl _

-- transitivity

_∾_ : ∀{Γ : Con}{A B C : Ty Γ}{a : Tm A}{b : Tm B}{c : Tm C} → a ≅ b → b ≅ c → a ≅ c
_∾_ {Γ} {.C} {.C} {C} {.c} {.c} {c} (refl .c) (refl .c) = refl c

-- "coercion"

_⟦_⟫ : {Γ : Con}{A B : Ty Γ}(a : Tm A) → A ≡ B → Tm B 
a ⟦ refl ⟫ = a

{-
-- with this we know p is irrelevant
rm-subst : {Γ : Con}{A B : Ty Γ}{a : Tm A}(p : A ≡ B) → subst Tm p a ≅ a
rm-subst refl = refl _
-}

-- namely coherence operator (the same as above)

cohOp : {Γ : Con}{A B : Ty Γ}{a : Tm A}(p : A ≡ B) → a ⟦ p ⟫ ≅ a
cohOp refl = refl _


-- reflexive : {Γ : Con}{A : Ty Γ}{a a' : Tm A} → a ≅ a' → a ≡ a'
-- reflexive (refl a) = refl

cong≅ : ∀{Γ Δ}{A : Ty Γ}{γ δ : Δ ⇒ Γ}(f : (x : Δ ⇒ Γ) → Tm (A [ x ]T)) → γ ≡ δ → f γ ≅ f δ
cong≅ f refl = refl _

-- cong by context morphism

_◃_ : {Γ Δ : Con}{A B : Ty Γ}{a : Tm A}{b : Tm B}(δ : Δ ⇒ Γ) → a ≅ b → a [ δ ]tm ≅ b [ δ ]tm
_ ◃ (refl _) = refl _ 

infixl 7 _,_

data Con where
  ε   : Con
  _,_ : (Γ : Con)(A : Ty Γ) → Con

--weakening rule

_+T_  : {Γ : Con}(A : Ty Γ)           → (B : Ty Γ) → Ty (Γ , B)
_+tm_ : {Γ : Con}{A : Ty Γ}(a : Tm A) → (B : Ty Γ) → Tm (A +T B)
_+S_  : {Γ : Con}{Δ : Con}(δ : Γ ⇒ Δ) → (B : Ty Γ) → (Γ , B) ⇒ Δ


data Ty Γ where
  *   : Ty Γ -- • can be type of any context
  hom : {A : Ty Γ}(a b : Tm A) → Ty Γ

-- type weakening rule

*         +T B = *
(hom a b) +T B = hom (a +tm B) (b +tm B)

-- the equality of hom
{-
_*[_] : {Γ : Con}{A B : Ty Γ} → (A ≡ B) → Tm A → Tm B
p *[ a ]
-}
hom≡ : {Γ : Con}{A A' : Ty Γ}(p : A ≡ A')
                {a : Tm A}{a' : Tm A'}(q : a ≅ a')
                {b : Tm A}{b' : Tm A'}(r : b ≅ b')
                → hom a b ≡ hom a' b'
hom≡ refl (refl a) (refl b) = refl

data Var where
  v0 : {Γ : Con}{A : Ty Γ} → Var (A +T A)
  vS : {Γ : Con}{A : Ty Γ}(x : Var A){B : Ty Γ} → Var (A +T B)


data Tm where
  var : {Γ : Con}{A : Ty Γ} → Var A → Tm A
--  var : {Γ : Con}{A B : Ty Γ} → Var (A +T B) → Tm (A +T B) -- why not use this?
  JJ  : {Γ Δ : Con} → isContr Δ → (δ : Γ ⇒ Δ) → (A : Ty Δ) → Tm (A [ δ ]T)

data isContr where
--  c•   : isContr ε   -- do we really need this?
  c*  : isContr (ε , *) -- actually we don't need this because * is already in • ps2: we need this....
  ext : {Γ : Con} → isContr Γ → {A : Ty Γ}(x : Var A) 
      → isContr ((Γ , A) , hom (var v0) (var (vS x {A})))

data _⇒_ where
  •   : {Γ : Con} → Γ ⇒ ε
  _,_ : {Γ Δ : Con}(δ : Γ ⇒ Δ){A : Ty Δ}(a : Tm (A [ δ ]T)) → Γ ⇒ (Δ , A)

cm-eq : {Γ Δ : Con}{γ δ : Γ ⇒ Δ}{A : Ty Δ}{a : Tm (A [ γ ]T)}{a' : Tm (A [ δ ]T)} → γ ≡ δ → a ≅ a' → _≡_ {_} {Γ ⇒ (Δ , A)} (γ , a) (δ , a')
cm-eq refl (refl _) = refl

-- basicJ : ∀{Γ : Con}(A : Ty ε) → Tm (A [ • {Γ} ]T)
-- basicJ = JJ c• •


-- composition of substitution

_⊚_ : ∀ {Γ Δ Θ} →  Δ ⇒ Θ → Γ ⇒ Δ → Γ ⇒ Θ

-- lemma 1 : syntactic substitution

[⊚]T : {Γ Δ Θ : Con}
         (θ : Δ ⇒ Θ)(δ : Γ ⇒ Δ)(A : Ty Θ)
       → A [ θ ⊚ δ ]T ≡ (A [ θ ]T)[ δ ]T

•       ⊚ δ = •
(δ , a) ⊚ δ' = (δ ⊚ δ') , a [ δ' ]tm ⟦ sym ([⊚]T δ δ' _) ⟫

-- freely move the weakening between S T tm


*       [ δ ]T = * 
hom a b [ δ ]T = hom (a [ δ ]tm) (b [ δ ]tm)



-- weakening doesn't introduce new variables

+T[,]T : {Γ Δ : Con}
         (A : Ty Δ)(δ : Γ ⇒ Δ)
         {B : Ty Δ}(b : Tm (B [ δ ]T))  
         → A [ δ ]T ≡ (A +T B) [ δ , b ]T


[+S]T : {Γ Δ : Con}
        (A : Ty Δ)(δ : Γ ⇒ Δ)
        (B : Ty Γ) 
        → A [ δ +S B ]T ≡ (A [ δ ]T) +T B


+tm[,]tm : {Γ Δ : Con}{A : Ty Δ}
         (a : Tm A)(δ : Γ ⇒ Δ)(B : Ty Δ)
         (c : Tm (B [ δ ]T))
         →  a [ δ ]tm ≅ (a +tm B) [ δ , c ]tm

[+S]tm : {Γ Δ : Con}{A : Ty Δ}
         (a : Tm A)(δ : Γ ⇒ Δ)
         (B : Ty Γ)
         → a [ δ +S B ]tm ≅ (a [ δ ]tm) +tm B


[+S]T *         δ B = refl
[+S]T (hom a b) δ B = hom≡ ([+S]T _ _ _) ([+S]tm a _ _) ([+S]tm b _ _)

•       +S B = •
(δ , a) +S B = (δ +S B) , (a +tm B) ⟦ sym ([+S]T _ _ _) ⟫

(var x)     +tm B = var (vS x)
(JJ cΔ δ A) +tm B = (JJ cΔ (δ +S B) A) ⟦ [+S]T _ _ _ ⟫


v0   [ δ , a ]V = a ⟦ +T[,]T _ _ _ ⟫
vS x [ δ , a ]V = (x [ δ ]V) ⟦ +T[,]T _ _ _ ⟫

[⊚]tm : {Γ Δ Θ : Con}
        (θ : Δ ⇒ Θ)(δ : Γ ⇒ Δ)(A : Ty Θ)(a : Tm A)
        →  a [ θ ⊚ δ ]tm ≅ (a [ θ ]tm) [ δ ]tm

[⊚]T θ δ * = refl
[⊚]T θ δ (hom {A} a b) = hom≡ ([⊚]T θ δ A) ([⊚]tm _ _ _ _) ([⊚]tm _ _ _ _)

+T[,]T * δ b = refl
+T[,]T (hom {A} a b) δ c = hom≡ (+T[,]T A δ c) (+tm[,]tm _ _ _ _) (+tm[,]tm _ _ _ _)

var x     [ δ ]tm = x [ δ ]V
JJ cΔ γ A [ δ ]tm = JJ cΔ (γ ⊚ δ) A ⟦ [⊚]T _ _ _ ⟫


lemma-v : {Γ Δ Θ : Con}
          (θ : Δ ⇒ Θ)(δ : Γ ⇒ Δ)(A : Ty Θ)(x  : Var A)
          → x [ θ ⊚ δ ]V ≅ (x [ θ ]V) [ δ ]tm
lemma-v (θ , a) δ .(A +T A) (v0 {Γ₁} {A}) = 
  cohOp (+T[,]T A (θ ⊚ δ) ((a [ δ ]tm) ⟦ sym ([⊚]T θ δ A) ⟫)) 
  ∾ (cohOp  (sym ([⊚]T θ δ A)) 
    ∾ ((δ ◃ cohOp (+T[,]T A θ a)) -¹))
lemma-v (θ , a) δ .(A +T B) (vS {Γ₁} {A} x {B}) = 
  cohOp (+T[,]T A (θ ⊚ δ) ( a [ δ ]tm ⟦ sym ([⊚]T θ δ B) ⟫))
  ∾ (lemma-v θ δ A x 
    ∾ ((δ ◃ cohOp (+T[,]T A θ a)) -¹))


⊚assoc : {Γ Δ Θ Δ₁ : Con}
        (γ : Θ ⇒ Δ₁)(θ : Δ ⇒ Θ)(δ : Γ ⇒ Δ)
        → (γ ⊚ θ) ⊚ δ ≡ γ ⊚ (θ ⊚ δ)
⊚assoc • θ δ = refl
⊚assoc (_,_ γ {A} a) θ δ = 
  cm-eq (⊚assoc γ θ δ) 
    (cohOp (sym ([⊚]T (γ ⊚ θ) δ A)) 
    ∾ ((δ ◃ cohOp (sym ([⊚]T γ θ A))) 
    ∾ ((cohOp (sym ([⊚]T γ (θ ⊚ δ) A)) 
    ∾ [⊚]tm θ δ (A [ γ ]T) a) -¹)))


[⊚]tm θ δ A (var x) = lemma-v θ δ A x
[⊚]tm θ δ .(A [ γ ]T) (JJ c γ A) = 
  cohOp ([⊚]T γ (θ ⊚ δ) A) 
  ∾ (((δ ◃ cohOp ([⊚]T γ θ A)) 
    ∾ (cohOp ([⊚]T (γ ⊚ θ) δ A) 
      ∾ cong≅ (λ x → JJ c x A) (⊚assoc γ θ δ))) -¹)


lem+t[]tm : ∀{Γ Δ Δ₁}(B : Ty Δ)(γ : Δ ⇒ Δ₁)(δ : Γ ⇒ Δ)(c : Tm (B [ δ ]T)) → (γ +S B) ⊚ (δ , c) ≡ γ ⊚ δ
lem+t[]tm B • δ c = refl
lem+t[]tm B (_,_ γ {A} a) δ c = 
  cm-eq (lem+t[]tm B γ δ c) 
  (cohOp (sym ([⊚]T (γ +S B) (δ , c) A)) 
    ∾ (((δ , c) ◃ cohOp (sym ([+S]T A γ B))) 
    ∾ ((cohOp (sym ([⊚]T γ δ A)) 
    ∾ +tm[,]tm a δ B c) -¹)))


+tm[,]tm (var x) δ B c = (cohOp (+T[,]T _ _ _)) -¹
+tm[,]tm (JJ x γ A) δ B c = cohOp ([⊚]T γ δ A) ∾ ((((δ , c) ◃ cohOp ([+S]T A γ B)) ∾ (cohOp ([⊚]T (γ +S B) (δ , c) A) ∾ cong≅ (λ t → JJ x t A) (lem+t[]tm B γ δ c))) -¹)


--lemma
cong+tm : ∀ {Γ : Con}{A B C : Ty Γ}{a : Tm A}(p : A ≡ B) → a +tm C ≅ a ⟦ p ⟫ +tm C
cong+tm refl = refl _
-- cong+tm {Γ} {.B} {B} {.b} {b} refl C (refl .b) = refl _


[+S]V : {Γ Δ : Con}{A : Ty Δ}
         (x : Var A)(δ : Γ ⇒ Δ)
         (B : Ty Γ)
         → x [ δ +S B ]V ≅ (x [ δ ]V) +tm B
[+S]V v0 (_,_ δ {A} a) B = cohOp (+T[,]T A (δ +S B) ((a +tm B) ⟦ sym ([+S]T A δ B) ⟫)) ∾ (cohOp (sym ([+S]T A δ B)) ∾ cong+tm (+T[,]T A δ a)) 
[+S]V (vS {A = A} x) (_,_ δ {C} a) B = cohOp (+T[,]T A (δ +S B) ((a +tm B) ⟦ sym ([+S]T C δ B) ⟫)) ∾ ([+S]V x δ B ∾ cong+tm (+T[,]T A δ a))



lem+Stm : ∀{Γ Δ Δ₁ : Con}(δ : Δ ⇒ Δ₁)(γ : Γ ⇒ Δ)(B : Ty Γ) → δ ⊚ (γ +S B) ≡ (δ ⊚ γ) +S B
lem+Stm • γ B = refl
lem+Stm (_,_ δ {A} a) γ B = 
  cm-eq (lem+Stm δ γ B) 
  (cohOp (sym ([⊚]T δ (γ +S B) A)) 
  ∾ (([+S]tm a γ B ∾ cong+tm (sym ([⊚]T δ γ A))) 
  ∾ (cohOp (sym ([+S]T A (δ ⊚ γ) B)) -¹)))

[+S]tm (var x) δ B = [+S]V x δ B
[+S]tm (JJ x δ A) γ B = cohOp ([⊚]T δ (γ +S B) A) ∾ ((cong≅ (λ t → JJ x t A) (lem+Stm δ γ B) ∾ (cohOp ([+S]T A (δ ⊚ γ) B) -¹)) ∾ cong+tm ([⊚]T δ γ A))
