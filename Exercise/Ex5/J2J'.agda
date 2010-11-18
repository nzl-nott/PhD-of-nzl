module J2J'
 where

open import Data.Product

infix 4 _≡_ 

data _≡_ {A : Set} : A → A → Set where
    refl : {a : A} → a ≡ a

J : {A : Set}(P : {x y : A} → x ≡ y → Set)
    → ({x : A} → P (refl {a = x})) 
    → {a b : A}(p : a ≡ b) → P p
J P m refl = m

subst : {A : Set}(P : A → Set){a b : A} → a ≡ b → P a → P b
subst P ab = J (λ {x} {y} _ → P x → P y) (λ p → p) ab

J' : {A : Set}{a : A}(Q : {x : A} → a ≡ x → Set)
    → Q {a} refl → {b : A}(ab : a ≡ b) → Q {b} ab
J' {A} {a} Q q ab = subst {Σ A (λ z → a ≡ z)} 
                          (λ p → Q (proj₂ p)) 
                          ? -- (J ((λ {x} {y} xy →  _≡_ {Σ A (λ z → x ≡ z)} (x , refl) (y , xy))) (λ {x} → refl) ab) 
                          q
