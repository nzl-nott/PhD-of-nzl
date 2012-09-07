open import Level
open import Relation.Binary.PropositionalEquality as PE hiding (refl; sym ; trans; isEquivalence)

module CategoryOfSetoid  (ext : Extensionality zero zero) where

open import Function
open import Relation.Binary.Core using (_⇒_)
import HProp
module hpx = HProp ext
open hpx

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

-- proof irrelevance (should be packaged with equivalence relation)
 
  PI : {x y : Carrier}{B : Set}(A : x ≈ y → B){p q : x ≈ y} → A p ≡ A q
  PI {x} {y} A {p} {q} with Uni (x ≈h y) {p} {q}
  PI A | PE.refl = PE.refl

  reflexive : _≡_ ⇒ _≈_
  reflexive PE.refl = refl

open HSetoid public renaming (refl to [_]refl; sym to [_]sym; _≈_ to [_]_≈_ ; _≈h_ to [_]_≈h_ ; Carrier to ∣_∣ ; trans to [_]trans)

[_]uip : ∀(Γ : HSetoid){a b : ∣ Γ ∣}{p q : [ Γ ] a ≈ b} → p ≡ q
[ Γ ]uip {a} {b} = Uni ([ Γ ] a ≈h b)



-- a variant with explicit arguments for proofs (for speficific use)
record HSetoid' : Set₁ where
  constructor _,_,_,_,_
  infix 4 _≈h_
  field
    Carrier : Set
    _≈h_     : Carrier → Carrier → HProp
    refl    : (x : Carrier) → < x ≈h x >
    sym     : (x y : Carrier) → < x ≈h y > → < y ≈h x >
    trans   : (x y z : Carrier) → < x ≈h y > → < y ≈h z > → < x ≈h z >
  
transVariant : HSetoid' → HSetoid
transVariant (Carrier , _≈h_ , refl , sym , trans) = Carrier , _≈h_ , (λ {x} → refl x) , (λ {x} {y} → sym x y) , (λ {x} {y} {z} → trans x y z)


-- Arrow between HSetoid

infix 5 _⇉_

record _⇉_ (A B : HSetoid) : Set where
  constructor fn:_resp:_
  field
    fn   : ∣ A ∣ → ∣ B ∣
    resp : {x y : ∣ A ∣} → 
           [ A ] x ≈ y → 
           [ B ] fn x ≈ fn y
open _⇉_ public renaming (fn to [_]fn ; resp to [_]resp)

-- identity

idCH : {Γ : HSetoid} → Γ ⇉ Γ 
idCH = record { fn = id; resp = id}

-- composition

infixl 5 _∘c_

_∘c_ : ∀{Γ Δ Z} → Δ ⇉ Z → Γ ⇉ Δ →  Γ ⇉ Z
yz ∘c xy = record 
           { fn = [ yz ]fn ∘ [ xy ]fn
           ; resp = [ yz ]resp ∘ [ xy ]resp
           }


-- verification of categorical laws

id₁ : ∀ {Γ Δ}(ch : Γ ⇉ Δ) → ch ∘c idCH ≡ ch
id₁ ch = PE.refl

id₂ : ∀ {Γ Δ}(ch : Γ ⇉ Δ) → idCH ∘c ch ≡ ch
id₂ ch = PE.refl

comp : ∀ {Γ Δ Φ Ψ} (f : Γ ⇉ Δ) (g : Δ ⇉ Φ) (h : Φ ⇉ Ψ)
       → h ∘c g ∘c f ≡ h ∘c (g ∘c f)
comp f g h = PE.refl
