module nuo2-2 where


-- Implement subst, assume idUni and prove J.

data Id (A : Set) : A → A → Set where
  refl : (a : A) → Id A a a

id : {A : Set} → A → A
id = λ x → x

subst : (A : Set)(a b : A)(p : Id A a b)
        (B : A → Set) → B a → B b
subst A .b b (refl .b) B = id

sym : (A : Set) → (a b : A) → Id A a b → Id A b a
sym A a b p = subst A a b p (λ b' → Id A b' a) (refl a)

trans : (A : Set) → (a b c : A) → Id A a b → Id A b c → Id A a c
trans A a b c p q = subst A b a (sym A a b p) (λ x → Id A x c) q

postulate idUni : (A : Set)(a : A)(p : Id A a a) → Id (Id A a a) p (refl a)

J-l : (A : Set)(P : (a b : A) → Id A a b → Set)
    → ((a : A) → P a a (refl a))
    → (a : A)(p : Id A a a) → P a a p
J-l A P m a p = subst (Id A a a) (refl a) p (sym (Id A a a) p (refl a) (idUni A a p)) (λ x → P a a x) (m a)
--K

J : (A : Set)(P : (a b : A) → Id A a b → Set)
    → ((a : A) → P a a (refl a))
    → (a b : A)(p : Id A a b) → P a b p
J A P m a b p = (subst A a b p (λ x → (q : Id A a x) → P a x q) (J-l A P m a)) p
