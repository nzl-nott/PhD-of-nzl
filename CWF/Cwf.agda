
{-# OPTIONS --type-in-type #-}

module CwF where


open import Cats.Category
open import Cats.Functor renaming (Functor to _⇨_)
open import Cats.Duality
open import Cats.Examples.Category
open import Data.Product
open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.HeterogeneousEquality as ht using (≅-to-≡) renaming (_≅_ to _≋_; refl to hrefl)

open Category renaming (obj to ∣_∣ ; hom to Hom[_]_⇨_)
open Functor


subst-assoc : ∀{A : Set}(P : A → Set){a b c : A}(p : a ≡ b)(q : b ≡ c){x : P a} → subst P (trans p q) x ≡ subst P q (subst P p x)
subst-assoc {A} P {.c} {.c} {c} refl refl {x} = refl

subst-sym : ∀{A : Set}(P : A → Set){a b : A}(p : a ≡ b){x : P b}{y : P a} → x ≡ subst P p y → subst P (sym p) x ≡ y
subst-sym P refl refl = refl

-- Product Equality split

PE-split : {A : Set}{B : A → Set}{p q : Σ A B} → p ≡ q → Σ (proj₁ p ≡ proj₁ q) (λ eq1 → subst B eq1 (proj₂ p) ≡ proj₂ q)
PE-split {A} {B} {.p} {p} refl = refl , refl


-- injection for function equality

injection : {A B : Set}{f g : A → B} → (f ≡ g) → ((a : A) → f a ≡ g a)
injection refl a = refl


-- families of sets (indexed sets)

FSets : Set₁
FSets = Σ[ I ∶ Set ] (I → Set)

-- morphisms between Families of sets

_⇉_ : FSets → FSets → Set
(I , f) ⇉ (J , g) = 
  Σ[ i-map ∶ (I → J) ]
    ((i : I) → f i → g (i-map i))

FId :  (As : FSets) → As ⇉ As
FId _ = (λ x → x) , (λ _ x → x)

F∘ : (α : FSets) {β : FSets} (γ : FSets) → β ⇉ γ → α ⇉ β → α ⇉ γ
F∘ _ _ (i-map1 , s-map1) (i-map2 , s-map2) = i-map1 ∘ i-map2 , (λ i x → s-map1 _ (i x)) ∘ s-map2

Fam : Category
Fam = record
      { obj       = FSets
      ; hom       = _⇉_
      ; id        = FId
      ; [_⇒_]_∘_   = F∘
      ; isCategory = record
                     { id₁ = λ _ _ _ → refl
                     ; id₂ = λ _ _ _ → refl
                     ; comp = λ _ _ _ _ _ → refl
                     }
      }


record CWF : Set₁ where
  field
    C : Category
    T : (Op C) ⇨ Fam
    ◇ : ∣ C ∣
    ◇isTerminal : ∀ A → Σ[ γ ∶ Hom[ C ] A ⇨ ◇ ] ((δ : Hom[ C ] A ⇨ ◇) → γ ≡ δ)

-- 1. Context and Context morphism

  Con       = ∣ C ∣
  _⇒_       = Hom[_]_⇨_ C
  [_⇨_]_∘CH_ = [_⇒_]_∘_ C
  
  _⊚_ : {Γ Δ Θ : Con}(γ : Δ ⇒ Θ)(δ : Γ ⇒ Δ) → Γ ⇒ Θ
  _⊚_ {Γ} {Δ} {Θ} γ δ = [ Γ ⇨ Θ ] γ ∘CH δ

  ε = ◇ -- empty Context

  isCat = isCategory C

-- 2. object part of the Functor T

  TObj : FunctorObj T
  TObj = mapObj T

-- Types are indexs

  Ty : Con → Set
  Ty Γ = proj₁ (TObj Γ)

-- Terms are indexed sets

  Tm : {Γ : Con}(A : Ty Γ) → Set
  Tm {Γ} = proj₂ (TObj Γ)


-----------------------------------------------------------------
-- JM equality for Terms (maybe useless)
  _≅_ : {Γ : Con}{A B : Ty Γ}{p : A ≡ B} → Tm A → Tm B → Set
  _≅_ {Γ} {.B} {B} {refl} a b = a ≡ b
-----------------------------------------------------------------

-- 3. homomorphism part of the Functor T

  THom : FunctorHom T
  THom = mapHom T

-- Type substitution

  _[_]T : {Γ Δ : Con} → Ty Δ → (γ : Γ ⇒ Δ) → Ty Γ
  A [ γ ]T = proj₁ (THom _ _ γ) A

-- Term substitution

  _[_]tm : {Γ Δ : Con}{A : Ty Δ} → Tm A → (γ : Γ ⇒ Δ) → Tm (A [ γ ]T)
  t [ γ ]tm = proj₂ (THom _ _ γ) _ t

-- substitution substitution is just composition

  _[_]S : {Γ Δ Θ : Con}(γ : Δ ⇒ Θ)(δ : Γ ⇒ Δ) → Γ ⇒ Θ
  γ [ δ ]S = γ ⊚ δ 

-- properties of susbstitution

-- empty Substitution

  ⋆ : {Γ : Con} → Γ ⇒ ε
  ⋆ {Γ} = proj₁ (◇isTerminal Γ)

  ⋆-zero : {Γ Δ : Con}{δ : Δ ⇒ Γ} → ⋆ ⊚ δ ≡ ⋆
  ⋆-zero {Γ} {Δ} {δ} = sym (proj₂ (◇isTerminal Δ) (⋆ ⊚ δ))

-- T is Functor
  
  isF = isFunctor T

-- 1. identity Context morphism

  IdCm : {Γ : Con} → Γ ⇒ Γ
  IdCm {Γ} = id C Γ

-- it is id

  Id-r : ∀{Γ Δ : Con}(γ : Γ ⇒ Δ) → γ ⊚ IdCm ≡ γ
  Id-r γ = id₁ isCat _ _ γ

  Id-l : ∀{Γ Δ : Con}(γ : Γ ⇒ Δ) → IdCm ⊚ γ ≡ γ
  Id-l γ = id₂ isCat _ _ γ

-- For types and terms

  Id-Ty : (Γ : Con)(A : Ty Γ) → A [ IdCm ]T ≡ A
  Id-Ty Γ A rewrite mapId isF Γ = refl -- refl -- = injection (proj₁ (PE-split (mapId isF Γ)))

  Id-Tm : (Γ : Con)(A : Ty Γ)(t : Tm A) → subst Tm (Id-Ty Γ A) (t [ IdCm ]tm) ≡ t
  Id-Tm Γ A t rewrite mapId isF Γ = refl -- {!mapId isF Γ!} -- subst (λ x → x A t ≋ t) {! (proj₂ (PE-split (mapId isF Γ)))!} hrefl -- injection (proj₂ (PE-split (mapId isF Γ)))


-- associativity of composition of context morphism

  assoc : {Γ Δ Φ Θ : Con}(γ : Γ ⇒ Δ)(δ : Δ ⇒ Φ)(θ : Φ ⇒ Θ)
          → (θ ⊚ δ) ⊚ γ ≡ θ ⊚ (δ ⊚ γ)
  assoc = comp isCat _ _  

  assoc-Ty : {Γ Δ Φ : Con}(A : Ty Γ)(γ : Δ ⇒ Γ)(δ : Φ ⇒ Δ) →
              A [ γ ⊚ δ ]T ≡ A [ γ ]T [ δ ]T
  assoc-Ty {Γ} {Δ} {Φ} A γ δ rewrite map∘ isF Γ Φ γ δ = refl

  assoc-Tm : {Γ Δ Φ : Con}{A : Ty Γ}(t : Tm A)(γ : Δ ⇒ Γ)(δ : Φ ⇒ Δ) →
              subst Tm (assoc-Ty A γ δ) (t [ γ ⊚ δ ]tm) ≡ t [ γ ]tm [ δ ]tm
  assoc-Tm {Γ} {Δ} {Φ} {A} t γ δ rewrite map∘ isF Γ Φ γ δ = refl


  cong-sub-Ty : {Γ Δ : Con}{A : Ty Δ}{γ δ : Γ ⇒ Δ} → γ ≡ δ → A [ γ ]T ≡ A [ δ ]T
  cong-sub-Ty refl = refl

  cong-sub-Tm : {Γ Δ : Con}{A : Ty Δ}{a : Tm A}{γ δ : Γ ⇒ Δ} → (p : γ ≡ δ) → subst Tm (cong-sub-Ty p) (a [ γ ]tm) ≡ a [ δ ]tm
  cong-sub-Tm refl = refl

  open Category CAT renaming ([_⇒_]_∘_ to [_⇒_]_F∘_)



record _withContextComprehension (cwf : CWF) : Set where
  open CWF cwf
  field
    _∙_ : (Γ : Con)(A : Ty Γ) → Con -- Context comprehension operation
    p  : {Γ : Con}{A : Ty Γ} → (Γ ∙ A) ⇒ Γ
    q  : {Γ : Con}{A : Ty Γ} → Tm (A [ p ]T)

    _∙CM_ : {Γ Δ : Con}{A : Ty Γ} → (γ : Δ ⇒ Γ) → Tm (A [ γ ]T) → Δ ⇒ (Γ ∙ A) -- Context morphism construction

    η-pq : {Γ : Con}{A : Ty Γ} → p ∙CM q ≡ IdCm {Γ ∙ A} -- eta law for pq

    pCM : {Γ Δ : Con}{A : Ty Γ}(γ : Δ ⇒ Γ)(a : Tm (A [ γ ]T)) → p ⊚ (γ ∙CM a) ≡ γ -- p (γ , a) = a
    qCM : {Γ Δ : Con}{A : Ty Γ}(γ : Δ ⇒ Γ)(a : Tm (A [ γ ]T)) → subst Tm (trans (sym (assoc-Ty _ _ _)) (cong-sub-Ty (pCM _ a))) (q [ (γ ∙CM a) ]tm) ≡ a -- q (γ  , a) = a
    
  --weakening rule

  _+T_ : {Γ : Con}(A : Ty Γ) → (B : Ty Γ) → Ty (Γ ∙ B)
  A +T _ = A [ p ]T

  _+tm_ : {Γ : Con}{A : Ty Γ}(a : Tm A) → (B : Ty Γ) → Tm (A +T B)
  a +tm _ = a [ p ]tm

  _+S_ : {Γ : Con}{Δ : Con}(δ : Γ ⇒ Δ) → (B : Ty Γ) → (Γ ∙ B) ⇒ Δ
  δ +S _ = δ ⊚ p

  [+S]T : {Γ Δ : Con}{A : Ty Δ}{δ : Γ ⇒ Δ}{B : Ty Γ} 
          → A [ δ +S B ]T ≡ (A [ δ ]T) +T B
  [+S]T  = assoc-Ty _ _ _

  [+S]tm : {Γ Δ : Con}{A : Ty Δ}(a : Tm A){δ : Γ ⇒ Δ}
           {B : Ty Γ}
           → subst Tm [+S]T (a [ δ +S B ]tm) ≡ (a [ δ ]tm) +tm B
  [+S]tm a = assoc-Tm _ _ _


  +T[,]T : {Γ Δ : Con}
           {A : Ty Δ}{δ : Γ ⇒ Δ}
           {B : Ty Δ}{b : Tm (B [ δ ]T)} 
         → (A +T B) [ δ ∙CM b ]T ≡ A [ δ ]T
  +T[,]T = trans (sym (assoc-Ty _ _ _)) (cong-sub-Ty (pCM _ _))

  +tm[,]tm : {Γ Δ : Con}{A : Ty Δ}
             {a : Tm A}{δ : Γ ⇒ Δ}{B : Ty Δ}
             {c : Tm (B [ δ ]T)}
             → subst Tm +T[,]T ((a +tm B) [ δ ∙CM c ]tm) ≡ a [ δ ]tm 
  +tm[,]tm = trans (trans (subst-assoc Tm (sym (assoc-Ty _ _ _)) (cong-sub-Ty (pCM _ _))) (cong (subst Tm (cong-sub-Ty (pCM _ _))) (subst-sym Tm (assoc-Ty _ _ _) (sym (assoc-Tm _ _ _))))) (cong-sub-Tm (pCM _ _))

  -- should write dependent types first

  _[_]DT : {Γ : Con}{A : Ty Γ} → Ty (Γ ∙ A) → Tm A → Ty Γ
  _[_]DT B a = B [ IdCm ∙CM subst Tm (sym (Id-Ty _ _)) a ]T

record _withΣtypes (cwf : CWF)(cc : cwf withContextComprehension) : Set where
  open CWF cwf
  open _withContextComprehension cc
  field
    ΣT    : {Γ : Con}(A : Ty Γ)(B : Ty (Γ ∙ A)) → Ty Γ
    _,,_  : {Γ : Con}(A : Ty Γ)(B : Ty (Γ ∙ A)) → (a : Tm A) → Tm (B [ a ]DT) → Tm (ΣT A B)
    prj₁  : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ∙ A)} → Tm (ΣT A B) → Tm A
    prj₂  : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ∙ A)} → (t : Tm (ΣT A B)) → Tm (B [ prj₁ t ]DT)



record _withProp (cwf : CWF)(cc : cwf withContextComprehension) : Set where
  open CWF cwf
  open _withContextComprehension cc
  field
    is-Prop : {Γ : Con} → Ty Γ → Set


 --    prj₁ ,, prj₂

-- prove : any two quotients should be isomorphic ?


-- if Q is a quotient in the original type theory, it should also be a quotient in setoid model

-- find whether there is a counter example: without quotients, any definable quotients are split.


-- something is true when we don't have quotients, fails when we have quotients
