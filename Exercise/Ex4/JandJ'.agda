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

Q : (A : Set)(a : A)(P : (b : A) → Id A a b → Set) → (b : A) → Set
Q A a P b = Σ (Id A a b) (λ p' → P b p')


q : {A : Set}{a : A}(P : (b : A) → Id A a b → Set){b : A} → (p : Id A a b) → (m : P b p) → Q A a P b
q P p m = p , m


lemmax : (A : Set)(a : A)(B : A → Set)(t : B a) → Id (B a) (subst A a a (refl a) B t) t
lemmax A a B t = refl t

lemmay : (M N : Set)(m : M)(n : N) → Id M (proj₁ (m , n)) m
lemmay M N m n = refl m

lemmaz : (A : Set)(a : A)(p q : Id A a a)(h : Id A a a → Id (Id A a a) p q)→ Id (Id (Id A a a) p q) (h (refl a))  (refl (refl a)) → (p : Id A a a) → h p
lemmaz A a H h = ?

lemma : (A : Set)(a : A) → (P : (b : A) → Id A a b → Set)
  → (m : P a (refl a)) → (b : A)(p : Id A a b) →
  Id (Id A a b) (proj₁ (subst A a b p (λ x → Q A a P x) (q P (refl a) m))) p


lemma A a P m b p = (subst A a b p (λ x → (p' : Id A a x) → Id (Id A a x) (proj₁ (subst A a x p' (λ x' → Q A a P x') ((refl a) , m))) p') (λ p' → {!!})) p

-- (J A (λ a' b' x → (t : Id A a a') →  (p' : Id A a b') → (m' : P a (refl a)) → Id (Id A a b') (proj₁ (subst A a b' p' (λ x' → Q A a P x') ((refl a) , m'))) p') (λ a' t p' m' → {!!}) a b p) ( (refl a) p m)

J'Id : (A : Set)(a : A) → (P : (b : A) → Id A a b → Set)
  → P a (refl a)
  → (b : A)(p : Id A a b) → P b p
J'Id A a P m b p = subst (Id A a b) (proj₁ (subst A a b p (λ x → Q A a P x) (q P (refl a) m))) p (lemma A a P m b p) (λ x' → P b x') (proj₂ (subst A a b p (λ x → Q A a P x)
 (q P (refl a) m)))

-- Id (Id A a b) (proj₁ (subst A a b p (λ x → Q A a P x) (q A a P a (refl a) m)))
-- = p
-- x = p
-- (J A (λ a' b' x' → (b' : A) → (x' : Id A a b') → (m' : P a (refl a)) → Id (Id A a b') (proj₁ (q A a P b' x' {!m'!})) x') ({!!}) a b p) b p m


-- (subst A a b p (λ x → (x : A) → (p' : Id A a x) → P x p') (λ b' p' → {!!})) b p
-- lemma A a b' a P (refl a) p' m
{-


lemma : (A : Set)(a b' c : A)(P : (b : A) → Id A c b → Set)(p1 : Id A c a)(p2 : Id A c b') → P a p1 → P b' p2
lemma A a b' c P p1 p2 m = (subst A a b' (trans A a c b' (sym A c a p1) p2) (λ x → (p2' : Id A c x) → P a p1 → P x p2') (λ p2' x → {!!})) p2 m

lemma2 : (A : Set)(a : A)(P : (b : A) → Id A a b → Set) → (p1 : Id A a a) → P a p1 → (b' : A) → (p2 : Id A a b') → P b' p2
lemma2 A a P p1 m b' p2 = (subst A a b' p2 (λ x → (x' : A) → (p2' : Id A a x) → P x p2') (λ x' → {!!})) b' p2

J'Id-l : (A : Set)(a : A) → (P : (b : A) → Id A a b → Set)
  → P a (refl a)
  → (p : Id A a a) → P a p
J'Id-l A a P m p = {!!}

J'lemma : (A : Set)(a : A)(P : (c b : A) → Id A a c → Id A c b → Set)
    → ((e : A) → (p' : Id A a e) → P e e p' (refl e))
    → (f b : A) → (p'' : Id A a f) → (p : Id A f b) → P f b p'' p
J'lemma A a P m f b p'' p = J A (λ a' b' x → P {!!} {!!} {!!} {!!}) (λ a' → {!!}) a b (trans A a f b p'' p)

J'Id : (A : Set)(a : A) → (P : (b : A) → Id A a b → Set)
  → P a (refl a)
  → (b : A)(p : Id A a b) → P b p
J'Id A a P m b p = J'lemma A a (λ c b' x x' → P b' (trans A a c b' x x')) (λ e p' → subst A a e p' (λ x → P x {!refl!}) m) a b (refl a) p
-}

-- (J A (λ a' b' x → (a' : A) → {!!}) (λ a' a0 → {!!}) a b p) a P m b p
-- J A (λ a' b x → {!!}) {!!} {!!}


{-
Try to derive J' from J.
-}
