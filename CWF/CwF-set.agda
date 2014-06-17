{-# OPTIONS --type-in-type #-}

module CWFstructure where

open import Cats.Category
open import Cats.Functor
open import Cats.Duality
open import Cats.Examples.Category
open import Data.Product
open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality hiding ([_])

open Category
open Functor
open IsFunctor

-- congruence of application or ext-inv

congApp : {A : Set}{B : A → Set}{f g : (x : A) → B x} → f ≡ g → ∀ x → f x ≡ g x
congApp refl x = refl

record _hasTerminal (C : Category) : Set where
  field
    Terminal : obj C
    isTerminal : ∀ a → hom C a Terminal
open _hasTerminal

-- families of sets


FamSets = Σ[ I ∶ Set ] (I → Set)

{-
record FamSets : Set₁ where
  constructor [i=_]_
  field
    I : Set
    B : I → Set
open FamSets
-}

FShom : FamSets → FamSets → Set
FShom (I1 , B1) (I2 , B2) = Σ (I1 → I2) (λ fI → (x : I1) → B1 x → B2 (fI x))

Fam : Category
Fam = record
      { obj       = FamSets
      ; hom       = FShom
      ; id        = λ α → (λ x → x) , (λ x x' → x')
      ; [_⇒_]_∘_   = λ α γ x x' → proj₁ x ∘ proj₁ x' , λ t → proj₂ x (proj₁ x' t) ∘ proj₂ x' t
      ; isCategory = record
                     { id₁ = λ α β f → refl
                     ; id₂ = λ α β f → refl
                     ; comp = λ α δ f g h → refl
                     }
      }



FamIndex : Functor Fam SET
FamIndex = record
           { mapObj = proj₁
           ; mapHom = λ α β x x' → proj₁ x x'
           ; isFunctor = record { mapId = λ α → ext (λ x → refl); map∘ = λ α γ f g → ext (λ x → refl) }
           }


record CWF : Set₁ where
  field
    C : Category
    T : Functor (Op C) Fam
    hT : C hasTerminal

-- 1. Context and Context morphism

  Con       = obj C
  ConHom    = hom C
  [_⇒_]_∘CH_ = [_⇒_]_∘_ C

-- 2. object part of the Functor T

  TObj : FunctorObj T
  TObj = mapObj T

-- Types are indexs

  Ty : Con → Set
  Ty Γ = proj₁ (TObj Γ)

-- Terms are indexed sets

  Tm : (Γ : Con)(A : Ty Γ) → Set
  Tm Γ = proj₂ (TObj Γ)

-- 3. homomorphism part of the Functor T

  THom : FunctorHom T
  THom = mapHom T

-- Type substitution

  _[_] : {Γ Δ : Con} → Ty Δ → (γ : ConHom Γ Δ) → Ty Γ
  _[_] {Γ} {Δ} A γ = proj₁ (THom Δ Γ γ) A

-- Term substitution

  _[_]m : {Γ Δ : Con}{A : Ty Δ} → Tm Δ A → (γ : ConHom Γ Δ) → Tm Γ (A [ γ ])
  _[_]m {Γ} {Δ} {A} t γ = proj₂ (THom Δ Γ γ) A t


-- terminal object : empty context
  ◇ : obj C
  ◇ = Terminal hT

  open Category CAT renaming ([_⇒_]_∘_ to [_⇒_]_F∘_)

  substComp : {Γ Δ Φ : Con}{A : Ty Γ}(γ : ConHom Δ Γ)(δ : ConHom Φ Δ) →
              A [ [ Φ ⇒ Γ ] γ ∘CH δ ] ≡ A [ γ ] [ δ ]
  substComp {Γ} {Δ} {Φ} {A} γ δ = {!!} -- injection (map∘ (isFunctor ([ Op C ⇒ SET ] FamIndex F∘ T)) Γ Φ γ δ) A 



record _withContextComprehension (cwf : CWF) : Set where
  open CWF cwf
  field
    _&_ : (Γ : Con)(A : Ty Γ) → Con -- Context comprehension operation
    all : (Γ : Con)(A : Ty Γ) → 
          Σ[ p ∶ ConHom (Γ & A) Γ ]
          Σ[ q ∶ Tm (Γ & A) (A [ p ]) ] (
          (Δ : Con)(γ : ConHom Δ Γ)(a : Tm Δ (A [ γ ]))
          → ∃! _≡_ (λ θ → Σ[ up1 ∶ [ Δ ⇒ Γ ] p ∘CH θ ≡ γ ] q [ θ ]m ≡ subst (λ x → Tm Δ x)(trans (subst (λ x → A [ γ ] ≡ A [ x ]) (sym up1) refl) (substComp p θ)) a))

{-
  p : (Γ : Con)(A : Ty Γ) → ConHom (Γ & A) Γ
  p Γ = proj₁ ∘ (all Γ)

  q   : (Γ : Con)(A : Ty Γ) → Tm (Γ & A) (A [ (p Γ A) ])
  q Γ = proj₁ ∘ proj₂ ∘ (all Γ)

-- universal properties
  up  : (Γ : Con)(A : Ty Γ) → (Δ : Con)(γ : ConHom Δ Γ)(a : Tm Δ (A [ γ ]))
        → ∃! _≡_ (λ θ → Σ[ up1 ∶ [ Δ ⇒ Γ ] (p Γ A) ∘CH θ ≡ γ ] (q Γ A) [ θ ]m ≡ subst (λ x → Tm Δ x)(trans (subst (λ x → A [ γ ] ≡ A [ x ]) (sym up1) refl) (substComp p θ)) a)
-- map∘
  up Γ = proj₂ ∘ proj₂ ∘ (all Γ)

-}

