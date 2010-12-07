module Equalities where
  
{-
It is easy to show that Id and Id' are isomorphic.

How is this related to the not so obvious derivation of J' for Id?
-}

data Id (A : Set) : A → A → Set where
  refl : (a : A) → Id A a a

J : (A : Set)(P : (a b : A) → Id A a b → Set)
    → ((a : A) → P a a (refl a))
    → (a b : A)(p : Id A a b) → P a b p
J A P m .b b (refl .b) = m b

data Id' (A : Set)(a : A) : A → Set where
  refl : Id' A a a


J' : (A : Set)(a : A) → (P : (b : A) → (Id' A a) b → Set)
  → P a refl
  → (b : A)(p : (Id' A a) b) → P b p
J' A .b P m b refl = m

subst : (A : Set)(a b : A)(p : Id A a b)
        (B : A → Set) → B a → B b
subst A a b p B = J A (λ a' b' _ → B a' → B b') (λ _ a → a) a b p

module Equalities where
  
{-
It is easy to show that Id and Id' are isomorphic.

How is this related to the not so obvious derivation of J' for Id?
-}

data Id (A : Set) : A → A → Set where
  refl : (a : A) → Id A a a

J : (A : Set)(P : (a b : A) → Id A a b → Set)
    → ((a : A) → P a a (refl a))
    → (a b : A)(p : Id A a b) → P a b p
J A P m .b b (refl .b) = m b

data Id' (A : Set)(a : A) : A → Set where
  refl : Id' A a a

J' : (A : Set)(a : A) → (P : (b : A) → Id' A a b → Set)
  → P a refl
  → (b : A)(p : Id' A a b) → P b p
J' A .b P m b refl = m

subst : (A : Set)(a b : A)(p : Id A a b)
        (B : A → Set) → B a → B b
subst A a b p B = J A (λ a' b' _ → B a' → B b') (λ _ a → a) a b p

φ : ∀ A → (a b : A) → Id A a b → Id' A a b
φ A a b p = subst A a b p (λ x → Id' A a x) refl

subst' : (A : Set)(a b : A)(p : Id' A a b)
        (B : A → Set) → B a → B b
subst' A a b p B x = J' A a (λ b' _ → B b') x b p

ψ : ∀ A → (a b : A) → Id' A a b → Id A a b
ψ A a b p = subst' A a b p (λ x → Id A a x) (refl a)

φψ : ∀ A → (a b : A)(p : Id' A a b) → Id _ (φ A a b (ψ A a b p)) p
φψ A a b p = J' A a (λ b p →  Id _ (φ A a b (ψ A a b p)) p) (refl _) b p

ψφ : ∀ A → (a b : A)(p : Id A a b) → Id _ (ψ A a b (φ A a b p)) p
ψφ A a b p = J A (λ a b p → Id _ (ψ A a b (φ A a b p)) p) (λ a' → refl _) a b p

J'Idaux : (A : Set)(a : A) → (P : (b : A) → Id A a b → Set)
     → P a (refl a)
     → (b : A)(p : Id A a b) → P b (ψ A a b (φ A a b p))
J'Idaux A a P m b p = J' A a (λ b' x → P b' (ψ A a b' x)) m b (φ A a b p)

J'Id : (A : Set)(a : A) → (P : (b : A) → Id A a b → Set)
     → P a (refl a)
     → (b : A)(p : Id A a b) → P b p
J'Id A a P m b p = subst _ ((ψ A a b (φ A a b p))) p (ψφ A a b p) (P b) (J'Idaux A a P m b p)φ : ∀ A → (a b : A) → Id A a b → Id' A a b
φ A a b p = subst A a b p (λ x → Id' A a x) refl

subst' : (A : Set)(a b : A)(p : Id' A a b)
        (B : A → Set) → B a → B b
subst' A a b p B x = J' A a (λ b' _ → B b') x b p

ψ : ∀ A → (a b : A) → Id' A a b → Id A a b
ψ A a b p = subst' A a b p (λ x → Id A a x) (refl a)

φψ : ∀ A → (a b : A)(p : Id' A a b) → Id _ (φ A a b (ψ A a b p)) p
φψ A a b p = J' A a (λ b p →  Id _ (φ A a b (ψ A a b p)) p) (refl _) b p

ψφ : ∀ A → (a b : A)(p : Id A a b) → Id _ (ψ A a b (φ A a b p)) p
ψφ A a b p = J A (λ a b p → Id _ (ψ A a b (φ A a b p)) p) (λ a' → refl _) a b p

J'Idaux : (A : Set)(a : A) → (P : (b : A) → Id A a b → Set)
     → P a (refl a)
     → (b : A)(p : Id A a b) → P b (ψ A a b (φ A a b p))
J'Idaux A a P m b p = J' A a (λ b' x → P b' (ψ A a b' x)) m b (φ A a b p)

J'Id : (A : Set)(a : A) → (P : (b : A) → Id A a b → Set)
     → P a (refl a)
     → (b : A)(p : Id A a b) → P b p
J'Id A a P m b p = subst _ ((ψ A a b (φ A a b p))) p (ψφ A a b p) (P b) (J'Idaux A a P m b p)