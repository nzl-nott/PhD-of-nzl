\begin{code}

{-# OPTIONS --type-in-type #-}


open import Level
open import Relation.Binary.PropositionalEquality as PE hiding (refl ; sym ; trans; isEquivalence; [_])

module CwF-presheaf (ext : Extensionality zero zero) where


open import Cats.Category
open import Cats.Functor renaming (Functor to _⇨_)
open import Cats.Duality
open import Data.Product renaming (<_,_> to ⟨_,_⟩)
open import Function

open import Relation.Binary.Core using (_≡_; _≢_)
open import Data.Unit

import CwF hiding (_⇉_)


open import CategoryOfSetoid ext public
open Category hiding (id)
open Functor


record IsFunctor'
  (C₁ : HSetoid)
  (C₂  : Category)

  (mapObj' : ∣ C₁ ∣
          → obj C₂)

  (mapHom' : ∀ α β
              → [ C₁ ] α ≈ β
              → hom C₂ (mapObj' α) (mapObj' β))
  : Set
  where
    open Category

    [_⇒_]'_∘₁_ : ∀ α {β} γ
              → [ C₁ ] β ≈ γ
              → [ C₁ ] α ≈ β
              → [ C₁ ] α ≈ γ
    [_⇒_]'_∘₁_ α γ p q = [ C₁ ]trans q p

    [_⇒_]'_∘₂_ : ∀ α {β} γ
              → hom C₂ β γ
              → hom C₂ α β
              → hom C₂ α γ
    [_⇒_]'_∘₂_ = [_⇒_]_∘_ C₂

    field
      mapId' : ∀ α
            → mapHom' α α ([ C₁ ]refl) ≡ Category.id C₂ (mapObj' α)

      map∘'  : ∀ α {β} γ (f : [ C₁ ] α ≈ β) (g : [ C₁ ] β ≈ γ)
            → mapHom' α γ ([ α ⇒ γ ]' g ∘₁ f) ≡ [ mapObj' α ⇒ mapObj' γ ]' (mapHom' β γ g) ∘₂ (mapHom' α β f)


record Functor' (C₁ : HSetoid)(C₂ : Category) : Set where
  open Category
  field
    mapObj'    : ∣ C₁ ∣
              → obj C₂

    mapHom'    : ∀ α β
              → [ C₁ ] α ≈ β
              → hom C₂ (mapObj' α) (mapObj' β)

    isFunctor' : IsFunctor' C₁ C₂ mapObj' mapHom'



-- families of setoids (indexed setoids)

FSetoids : Set₁
FSetoids = (X : HSetoid) → Σ[ I ∶ Functor' X Std ] Functor' ∣ I ∣ → HSetoid)

-- morphisms between Families of setoids

_⇉setoid_ : FSetoids → FSetoids → Set
_⇉setoid_ = {!!}
{-(I , f) ⇉setoid (J , g) = 
  Σ[ i-map ∶ (∣ I ∣ → ∣ J ∣) ]
    ((i : ∣ I ∣) → ∣ f i ∣ → ∣ g (i-map i) ∣)
-}

Fam-setoid : Category
Fam-setoid = {!!}
{-
CatC 
               FSetoids 
               _⇉setoid_ 
               (λ _ → id , (λ _ → id)) 
               (λ { _ _ (fty , ftm) (gty , gtm) → fty ∘ gty , (λ i x → ftm (gty i) (gtm i x))}) 
               (IsCatC 
                 (λ α β f → PE.refl) 
                 (λ α β f → PE.refl) 
                 (λ α δ f g h → PE.refl))
-}
record CWF-setoid : Set₁ where
  field
    T : (Op Std) ⇨ Fam-setoid
    ◇isTerminal : ∀ A → Σ[ γ ∶ A ⇉ ● ] ((δ : A  ⇉ ●) → γ ≡ δ)

  C = Op Std

-- 1. Context and Context morphism

  Con       = obj C
  ConHom    = hom C
  [_⇒_]_∘CH_ = [_⇒_]_∘_ C

-- 2. object part of the Functor T

  TObj : FunctorObj T
  TObj = mapObj T

-- Types are indexs

  Ty' : Con → HSetoid
  Ty' Γ = proj₁ (TObj Γ)

  Ty : Con → Set
  Ty Γ = ∣ Ty' Γ ∣

-- Terms are indexed sets

  Tm' : (Γ : Con)(A : Ty Γ) → HSetoid
  Tm' Γ = proj₂ (TObj Γ)

  
  Tm : (Γ : Con)(A : Ty Γ) → Set
  Tm Γ A = ∣ Tm' Γ A ∣

-- 3. homomorphism part of the Functor T

  THom : FunctorHom T
  THom = mapHom T

-- Type substitution

  _[_] : {Γ Δ : Con} → Ty Δ → (γ : Γ ⇉ Δ) → Ty Γ
  _[_] {Γ} {Δ} A γ = proj₁ (THom Δ Γ γ) A

-- Term substitution

  _[_]m : {Γ Δ : Con}{A : Ty Δ} → Tm Δ A → (γ : Γ ⇉ Δ) → Tm Γ (A [ γ ])
  _[_]m {Γ} {Δ} {A} t γ = proj₂ (THom Δ Γ γ) A t

-- empty substitution

  ⋆ : {Δ : Con} → Δ ⇉ ●
  ⋆ = record 
      { fn = λ _ → tt
      ; resp = λ _ → tt }


-- the empty substitution is unique

  uniqueHom : ∀ (Δ : Con) → (f : Δ ⇉ ●) → f ≡ ⋆
  uniqueHom Δ f = PE.refl

-- Context Comprehension

  _&_ : (Γ : Con) → Ty Γ → Con
  Γ & A = record 
        { Carrier = Σ[ x ∶ ∣ Γ ∣ ] {!A x!} -- ∣ {!A!} ∣
         ; _≈h_  = {!!} -- λ{(x , a) (y , b) → Σ'[ p ∶ x ≈h y ] [ fm y ] substT p a ≈h b}
         ; refl  = {!!} -- refl , (refl* _ _)
         ; sym   = {!!} --λ {(p , q) → (sym p) , [ fm _ ]trans (subst* _ ([ fm _ ]sym q)) trans-refl }
        ; trans = {!!} -- λ {(p , q) (m , n) → trans p m , [ fm _ ]trans ([ fm _ ]trans ([ fm _ ]sym (trans* _)) (subst* _ q)) n }
        }
        where 
          open HSetoid Γ
--          open Ty A     
\end{code}