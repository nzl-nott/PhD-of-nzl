module Palmgren where

open import Relation.Binary.Core
open import Relation.Nullary.Core

data Id (A : Set) : A → A → Set where
  refl : (a : A) → Id A a a

-- we have Identity elimination -- elimI

J : (A : Set)(P : (a b : A) → Id A a b → Set)
    → ((a : A) → P a a (refl a))
    → (a b : A)(p : Id A a b) → P a b p
J A P m .b b (refl .b) = m b

-- Identity coercion -- coercI

subst : (A : Set)(a b : A)(p : Id A a b)
        (B : A → Set) → B a → B b
subst A a b p B = J A (λ a' b' _ → B a' → B b') (λ _ a → a) a b p

--Identity mapping -- mapI

resp : (A B : Set) → (f : A → B) → (a b : A) → Id A a b → Id B (f a) (f b)
resp A B f a b p = J A (λ a' b' _ → Id B (f a') (f b')) (λ a' → refl (f a')) a b p

-- Identity composition -- cmpI

trans : (A : Set) → (a b c : A) → Id A a b → Id A b c → Id A a c
trans A a b c p q = subst A b c q (λ x → Id A a x) p

-- Identity inverse -- invI

sym : (A : Set) → (a b : A) → Id A a b → Id A b a
sym A a b p = J A (λ a' b' x → Id A b' a') refl a b p

-- A groupoid law.

invrI : (A : Set)(a b : A)(u : Id A a b) → Id (Id A b b) (trans A b a b (sym A a b u) u) (refl b)
invrI A a b u = J A (λ a b u → Id (Id A b b) (trans A b a b (sym A a b u) u) (refl b)) (λ b → refl (refl b)) a b u

-- Constancy lemma

con : (A : Set) → Dec A → A → A
con A (yes p) a = p
con A (no _ ) a = a

iscon : (A : Set) → (d : Dec A) → (a a' : A) → Id A (con A d a) (con A d a')
iscon A (yes p) a a' = refl p
iscon A (no ¬p) a a' with ¬p a
iscon A (no ¬p) a a' | ()


-- Collapse lemma

collaps : (A : Set)(f : A → A)
        (is_c : ∀ x x' → Id A (f x) (f x'))
        (g : A → A)
        (is_li : ∀ x → Id A (g (f x)) x)(a b : A) → Id A a b
collaps A f is_c g is_li a b = trans A a (g (f a)) b (sym A (g (f a)) a (is_li a)) (trans A (g (f a)) (g (f b)) b (resp A A g (f a) (f b) (is_c a b)) (is_li b))

-- Left inverse lemma

leftinv : (A : Set)(nt : (x y : A) → Id A x y → Id A x y) →
          (a b : A) → Id A a b → Id A a b
leftinv A nt a b v = trans A a a b (sym A a a (nt a a (refl a))) v

isleftinv : (A : Set)(nt : (a b : A) → Id A a b → Id A a b)(a b : A)(u : Id A a b)
            → Id(Id A a b) (leftinv A nt a b (nt a b u)) u
isleftinv A nt a b u = J A (λ a b u → Id (Id A a b) (leftinv A nt a b (nt a b u)) u) (λ x → invrI A x x (nt x x (refl x))) a b u


-- DI⊆CI-theorem

condi : (A : Set)(di : Decidable (Id A)) → 
        (x y : A)(u : Id A x y) → Id A x y
condi A di x y u = con (Id A x y) (di x y) u

-- Therorem 1.1

dici : (A : Set) → Decidable (Id A) →
      ∀ (x y : A)(u v : Id A x y) → Id (Id A x y) u v
dici A di x y u v = collaps (Id A x y) 
  (condi A di x y) (iscon (Id A x y) (di x y))
  (leftinv A (condi A di) x y) (isleftinv A (condi A di) x y) u v


--------------------------------------------------------------------------
--------------------------------------------------------------------------

-- 2. Axiomatizing UIP

K : {A : Set}{D : (x : A)(z : Id A x x) → Set}
    (d : (x : A) → D x (refl x))(a : A)(c : Id A a a) → D a c
K d a (refl .a) = d a

J² : {A : Set}{C : (x y : A)(u v : Id A x y) → Set}(d : (x : A) → C x x (refl x) (refl x)) → (a b : A) → (c c' : Id A a b) → C a b c c'
J² d a b c c' = {!!}