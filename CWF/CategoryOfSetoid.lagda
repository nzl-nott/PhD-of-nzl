\AgdaHide{
\begin{code}

{-# OPTIONS --type-in-type #-}

open import Level
open import Relation.Binary.PropositionalEquality as PE hiding (refl; sym ; trans; isEquivalence)

module CategoryOfSetoid  (ext : Extensionality zero zero) where

open import Cats.Category
open import Function
open import Relation.Binary.Core using (_⇒_)
open import Data.Empty
open import HProp ext public
open import Data.Unit

\end{code}
}

\subsection{Category of setoids}

\begin{code}

record HSetoid : Set₁ where
  constructor _,_,_,_,_
  infix 4 _≈h_ _≈_
  field
    Carrier : Set
    _≈h_     : Carrier → Carrier → HProp
    refl    : {x : Carrier} → < x ≈h x >
    sym     : {x y : Carrier} → < x ≈h y > → < y ≈h x >
    trans   : {x y z : Carrier} → < x ≈h y > → < y ≈h z > → < x ≈h z >
  
  _≈_ : Carrier → Carrier → Set
  a ≈ b = < a ≈h b >

  PI : {x y : Carrier}{B : Set}(A : x ≈ y → B){p q : x ≈ y} → A p ≡ A q
  PI {x} {y} A {p} {q} with Uni (x ≈h y) {p} {q}
  PI A | PE.refl = PE.refl

  reflexive : _≡_ ⇒ _≈_
  reflexive PE.refl = refl

open HSetoid public renaming (refl to [_]refl; sym to [_]sym; 
  _≈_ to [_]_≈_ ; _≈h_ to [_]_≈h_ ; Carrier to ∣_∣ ; trans to [_]trans)

rel : (A : HSetoid) → ∣ A ∣ → ∣ A ∣ → HProp
rel A a b = [ A ] a ≈h b

[_]uip : ∀(Γ : HSetoid){a b : ∣ Γ ∣}{p q : [ Γ ] a ≈ b} → p ≡ q
[ Γ ]uip {a} {b} = Uni ([ Γ ] a ≈h b)

\end{code}

Morphisms between HSetoids (Functors)

\begin{code}

infix 5 _⇉_

record _⇉_ (A B : HSetoid) : Set where
  constructor fn:_resp:_
  field
    fn   : ∣ A ∣ → ∣ B ∣
    resp : {x y : ∣ A ∣} → 
           [ A ] x ≈ y → 
           [ B ] fn x ≈ fn y
open _⇉_ public renaming (fn to [_]fn ; resp to [_]resp)

\end{code}

Identity

\begin{code}

idCH : {Γ : HSetoid} → Γ ⇉ Γ 
idCH = record { fn = id; resp = id}

\end{code}

Composition

\begin{code}

infixl 5 _∘c_

_∘c_ : ∀{Γ Δ Z} → Δ ⇉ Z → Γ ⇉ Δ → Γ ⇉ Z
yz ∘c xy = record 
           { fn = [ yz ]fn ∘ [ xy ]fn
           ; resp = [ yz ]resp ∘ [ xy ]resp
           }
\end{code}

Categorical laws

\begin{code}

id₁ : ∀ {Γ Δ}(ch : Γ ⇉ Δ) → ch ∘c idCH ≡ ch
id₁ ch = PE.refl

id₂ : ∀ {Γ Δ}(ch : Γ ⇉ Δ) → idCH ∘c ch ≡ ch
id₂ ch = PE.refl

comp : ∀ {Γ Δ Φ Ψ} (f : Γ ⇉ Δ) (g : Δ ⇉ Φ) (h : Φ ⇉ Ψ)
       → h ∘c g ∘c f ≡ h ∘c (g ∘c f)
comp f g h = PE.refl

_f≈_ :  ∀{Γ Δ : HSetoid} → (f g : Γ ⇉ Δ) → HProp
_f≈_ {Γ , _≈h_ , refl , sym , trans} 
     {Δ , _≈h₁_ , refl₁ , sym₁ , trans₁}
     (fn: fn resp: fresp) (fn: gn resp: gresp) 
  = record 
           { prf = (g : Γ) → < fn g ≈h₁ gn g >
           ; Uni = ext (λ g → Uni (fn g ≈h₁ gn g))
           }

\end{code}

Category of Setoids

\begin{code}


Std : Category
Std = CatC HSetoid _⇉_ (λ _ → idCH) (λ _ _ → _∘c_) 
      (IsCatC (λ α β f → PE.refl) 
      (λ α β f → PE.refl) 
      (λ α δ f g h → PE.refl))

\end{code}

Terminal object

\begin{code}

● : HSetoid
●   = record {
      Carrier = ⊤;
      _≈h_    = λ _ _ → ⊤';
      refl    = tt;
      sym     = λ _ → tt;
      trans   = λ _ _ → tt }


⋆ : {Δ : HSetoid} → Δ ⇉ ●
⋆ = record 
      { fn = λ _ → tt
      ; resp = λ _ → tt }

uniqueHom : ∀ (Δ : HSetoid) → (f : Δ ⇉ ●) → f ≡ ⋆
uniqueHom Δ f = PE.refl

\end{code}