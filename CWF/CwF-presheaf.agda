
{-# OPTIONS --type-in-type #-}


open import Level
open import Relation.Binary.PropositionalEquality as PE hiding (refl ; sym ; trans; isEquivalence; [_])

module CwF-presheaf (ext : Extensionality zero zero) where


open import Cats.Category
open import Cats.Functor renaming (Functor to _⇨_)
open import Cats.Duality
open import Data.Product renaming (<_,_> to ⟨_,_⟩)
open import Function

-- open import Relation.Binary
open import Relation.Binary.Core using (_≡_; _≢_)
open import Data.Unit

-- open import HProp ext

open import CwF hiding (_⇉_)
open import CwF-setoid ext

-- families of setoids (indexed setoids)

FSetoids : Set₁
FSetoids = Σ[ I ∶ HSetoid ] (∣ I ∣ → HSetoid)

-- morphisms between Families of setoids

_⇉setoid_ : FSetoids → FSetoids → Set
(I , f) ⇉setoid (J , g) = 
  Σ[ i-map ∶ (∣ I ∣ → ∣ J ∣) ]
    ((i : ∣ I ∣) → ∣ f i ∣ → ∣ g (i-map i) ∣)

Fam-setoid : Category
Fam-setoid = CatC 
               FSetoids 
               _⇉setoid_ 
               (λ _ → id , (λ _ → id)) 
               (λ { _ _ (fty , ftm) (gty , gtm) → fty ∘ gty , (λ i x → ftm (gty i) (gtm i x))}) 
               (IsCatC 
                 (λ α β f → PE.refl) 
                 (λ α β f → PE.refl) 
                 (λ α δ f g h → PE.refl))

record CWF-setoid : Set₁ where
  field
    T : (Op setoid-Cat) ⇨ Fam-setoid
    ◇isTerminal : ∀ A → Σ[ γ ∶ A ⇉ ● ] ((δ : A  ⇉ ●) → γ ≡ δ)

  C = Op setoid-Cat

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