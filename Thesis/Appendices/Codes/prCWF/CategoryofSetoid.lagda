\AgdaHide{
\begin{code}

module CategoryofSetoid where


open import Relation.Binary.PropositionalEquality as PE
  hiding ([_] ; refl; sym ; trans; isEquivalence)
open import Level
open import Data.Unit
open import Relation.Binary.HeterogeneousEquality using ()
\end{code}
}

\section{Metatheory}

Subset defined by a predicate $B$

\begin{code}
record Subset {a b} (A : Set a) 
       (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    prj₁ : A
    .prj₂ : B prj₁
open Subset public
\end{code}

Setoids 

\begin{code}
record Setoid : Set₁ where
  infix 4 _≈_
  field
    Carrier : Set
    _≈_     : Carrier → Carrier → Set
    .refl   : ∀{x} → x ≈ x
    .sym    : ∀{x y} → x ≈ y → y ≈ x
    .trans  : ∀{x y z} → x ≈ y → y ≈ z → x ≈ z
open Setoid public renaming 
     (Carrier to ∣_∣ ; _≈_ to [_]_≈_ ; refl to [_]refl;
     trans to [_]trans; sym to [_]sym) 
\end{code}

Morphisms between Setoids (Functors)


\begin{code}
infix 5 _⇉_

record _⇉_ (A B : Setoid) : Set where
  constructor fn:_resp:_
  field
    fn   : ∣ A ∣ → ∣ B ∣
    .resp : {x y : ∣ A ∣} → 
           ([ A ] x ≈ y) → 
           [ B ] fn x ≈ fn y
open _⇉_ public renaming (fn to [_]fn ; resp to [_]resp)
\end{code}

Terminal object

\begin{code}
● : Setoid
●   = record {
      Carrier = ⊤;
      _≈_    = λ _ _ → ⊤;
      refl    = tt;
      sym     = λ _ → tt;
      trans   = λ _ _ → tt }

⋆ : {Δ : Setoid} → Δ ⇉ ●
⋆ = record 
      { fn = λ _ → tt
      ; resp = λ _ → tt }

uniqueHom : ∀ (Δ : Setoid) 
          → (f : Δ ⇉ ●) → f ≡ ⋆
uniqueHom Δ f = PE.refl
\end{code}