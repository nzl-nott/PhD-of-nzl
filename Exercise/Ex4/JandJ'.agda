module JandJ' where

open import Data.Product

data Id (A : Set) : A → A → Set where
  refl : (a : A) → Id A a a

J : (A : Set)(P : (a b : A) → Id A a b → Set)
    → ((a : A) → P a a (refl a))
    → (a b : A)(p : Id A a b) → P a b p
J A P m .b b (refl .b) = m b

-- what is the difference to the library?

data Id' (A : Set)(a : A) : A → Set where
  refl : Id' A a a

J' : (A : Set)(a : A) → (P : (b : A) → Id' A a b → Set)
  → P a refl
  → (b : A)(p : Id' A a b) → P b p
J' A .b P m b refl = m

-- Exercise: Implement J using J'

id : {A : Set} → A → A
id = λ x → x

subst : (A : Set)(a b : A)(p : Id A a b)
        (B : A → Set) → B a → B b
subst A a b p B = J A (λ a' b' _ → B a' → B b') (λ _ → id) a b p

JId' : (A : Set)(P : (a b : A) → Id' A a b → Set)
    → ((a : A) → P a a refl)
    → (a b : A)(p : Id' A a b) → P a b p
-- implement J' using J.
JId' A P m a = J' A a (P a) (m a)


Pc : (A : Set)(a : A)(P : (b : A) → Id A a b → Set) → ((a b : A) → Id A a b → Set)
Pc A a P a' b' p = P a (refl a)

sym : (A : Set) → (a b : A) → Id A a b → Id A b a
sym A a b p = subst A a b p (λ b' → Id A b' a) (refl a)

trans : (A : Set) → (a b c : A) → Id A a b → Id A b c → Id A a c
trans A a b c p q = subst A b a (sym A a b p) (λ x → Id A x c) q

Q : (A : Set)(a : A) → Set
Q A a = Σ A (λ b → Id A a b)

J'Id : (A : Set)(a : A) → (P : (b : A) → Id A a b → Set)
  → P a (refl a)
  → (b : A)(p : Id A a b) → P b p
J'Id A a P m b p = subst (Q A a) (a , refl a) (b , p) (J A (λ a' b' x → Id (Q A a') (a' , refl a') (b' , x)) (λ a' → refl (a' , (refl a'))) a b p) (uncurry P) m