module nuo3 where

open import Data.Nat
open import Relation.Nullary

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

lem1 : (A : Set)(a b c : A) → Id' A b c → Id A a b → Id A a c
lem1 A a b c p = J' A b (λ c' x → Id A a b → Id A a c') id c p

lem2 :  (A : Set)(a b c : A) → Id' A a b → Id A a c → Id' A b c
lem2 A a b c p = J' A a (λ b' x → Id A a c → Id' A b' c) {!!} b p

subst' :  (A : Set)(a b : A)(p : Id' A a b)
        (B : A → Set) → B a → B b
subst' A a b p B ba = J' A a (λ b' _ → B b') ba b p

JbyJ' : (A : Set)(P : (a b : A) → Id A a b → Set)
    → ((a : A) → P a a (refl a))
    → (a b : A)(p : Id A a b) → P a b p
JbyJ' A P m a b p = J' A a (λ b' x → P a b' (J' A a (λ b0 x' → Id A a b0) (refl a) b' x)) (m a) b (lem2 A a a b refl p)

-- implement J' using J.

psi : (A : Set)(a b  : A) → Id A a b → Id' A a b
psi A = J A (λ a' b' _ → Id' A a' b') (λ _ → refl)


phi2 : (A : Set)(a b  : A) → Id' A a b → Id A a b
phi2 A a b p = {!!}

J'byJ : (A : Set)(a : A) → (P : (b : A) → Id' A a b → Set)
  → P a refl
  → (b : A)(p : Id' A a b) → P b p
J'byJ A a P m = J A (λ a' → {!P!}) {!!} {!!} {!!} {!!}

-- what happens if we add ext as a constructor for Id?

data IdE : (A : Set) → A → A → Set₁ where
  refl : {A : Set}(a : A) → IdE A a a
  ext : (A B : Set)(f g : A → B) → ((a : A) → IdE B (f a) (g a)) → IdE (A → B) f g

substE : (A : Set)(a b : A)(p : IdE A a b)
        (B : A → Set) → B a → B b
substE A .b b (refl .b) B x = x
substE .(A → B) f g (ext A B .f .g e) C x = {!!}

-- now we only use J, not pattern matching!

subst : (A : Set)(a b : A)(p : Id A a b)
        (B : A → Set) → B a → B b
subst A a b p B x = {!!}  -- only using J
--subst A .b b (refl .b) B x = x

sym : (A : Set) → (a b : A) → Id A a b → Id A b a
sym A a b p = {!!}

trans : (A : Set) → (a b c : A) → Id A a b → Id A b c → Id A a c
trans A a b c p q = {!!}

resp : (A B : Set) → (f : A → B) → (a b : A) → Id A a b → Id B (f a) (f b)
resp A B f a b p = {!!}

postulate
  Ext : {A : Set}{B : A → Set}{f g : (x : A) → B x}
        → ((x : A) → Id (B x) (f x) (g x)) 
        → Id ((x : A) → B x) f g


irr : ℕ
irr = J (ℕ → ℕ) (λ a b x → ℕ) (λ a → 0) (λ x → x) (λ x → x) (Ext refl)

irr-prf : ∀ n → ¬ Id ℕ irr n
irr-prf n eqt = {!eqt!}

{-
postulate
  ext : (A : Set)(B : A → Set)(f g : (x : A) → B x)
        → ((x : A) → Id (B x) (f x) (g x)) 
        → Id ((x : A) → B x) f g

idUni : (A : Set)(a : A)(p : Id A a a) → Id (Id A a a) p (refl a)
idUni A a p = {!!} -- try to prove from J
--idUni A a (refl .a) = refl (refl a) 

-- Implement subst, assume idUni and prove J.

-- TTI = implement subst, postulate ext and idUni.

-- encode the example in the beginning section 2 in Agda

-- try to read the rest and come up with some questions.

-- read section 3, what is the open problem?
-}
