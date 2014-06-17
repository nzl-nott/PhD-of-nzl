module ex7-3 where

open import Data.Product


data Id (A : Set) (a : A) : A → Set where
  refl : Id A a a


J : {A : Set}(P : (a b : A) → Id A a b → Set)
    → ((a : A) → P a a refl)
    → (a b : A)(p : Id A a b) → P a b p
J P m .b b refl = m b

id : {A : Set} → A → A
id a = a

subst :  {A : Set}(a b : A)(p : Id A a b)
        (B : A → Set) → B a → B b
subst a b p B = J (λ a b _ → B a → B b) (λ _ → id) a b p


[_] : {A : Set}{a b : A} → Id A a b → Id A b a
[_] {A} {a} {b} = J (λ a b _ → Id A b a) (λ _ → refl) a b


infix 5 _>=<_

_>=<_ : {A : Set}{a b c : A} → Id A a b → Id A b c → Id A a c
_>=<_ {A} {a} {b} {c} = J (λ a b _ → Id A b c → Id A a c) (λ _ → id) a b
--seems like an instance of subst
-- subst b c bc (Id A a) ab

-- Groupoid laws :


Λ : {A : Set}{a b : A}{p : Id A a b} → Id (Id A a b) (refl >=< p) p
Λ {A} {a} {b} {p} = refl

ρ : {A : Set}{a b : A}{p : Id A a b} → Id (Id A a b) (p >=< refl) p
ρ {A} {a} {b} {p} = J (λ a b p → Id (Id A a b) (J (λ a1 b1 _ → Id A b1 b → Id A a1 b) (λ _ → id) a b p refl) p) (λ _ → refl) a b p

Q : (A : Set)(b : A) → Set
Q A b = Σ[ a ∶ A ] Id A a b

qeq : {A : Set}(a b : A)(p : Id A a b) → Id (Q A b) (b , refl) (a , p)
qeq {A} a b p = (J (λ a b p → Id (Q A b) (b , refl) (a , p)) (λ _ → refl) a b p)


α : {A : Set}{a b c d : A}{ab : Id A a b}{bc : Id A b c}{cd : Id A c d} → Id (Id A a d) (ab >=< (bc >=< cd)) ((ab >=< bc) >=< cd)
α {A} {a} {b} {c} {d} {ab} {bc} {cd} = subst {Q A b} (b , refl) (a , ab) (qeq a b ab) (uncurry (λ a' ab' → Id (Id A a' d) (ab' >=< (bc >=< cd)) ((ab' >=< bc) >=< cd))) refl


-- syntax Id A a b = a ≡[ A ] b

-- syntax uncurry (λ x y → P) = λ[ x , y ]→ P

il : {A : Set}(a b : A)(p : Id A a b) → Id (Id A b b) ([ p ]  >=< p) refl
il {A} = J (λ _ b p → Id (Id A b b) ([ p ]  >=< p) refl) (λ _ → refl)

-- subst {Q A b} (b , refl) (a , p) (qeq a b p) (uncurry (λ a p → (Id (Id A b b) ([ p ] >=< p) refl))) refl

rl : {A : Set}(a b : A)(p : Id A a b) → Id (Id A a a) (p >=< [ p ]) refl
rl {A} = J (λ a _ p → Id (Id A a a) (p >=< [ p ]) refl) (λ _ → refl)

-- subst {Q A b} (b , refl) (a , p) (qeq a b p) (uncurry (λ a p → Id (Id A a a) (p >=< [ p ]) refl)) refl
