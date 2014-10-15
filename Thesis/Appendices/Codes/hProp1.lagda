\begin{code}

{-# OPTIONS --type-in-type #-}

module hProp1 where

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
import Data.Unit as U
import Data.Empty as E

isContr : (A : Set) → Set
isContr A = Σ[ p ∶ A ] (∀ a → a ≡ p)

is-hlevel : (n : ℕ)(A : Set) → Set
is-hlevel zero A = isContr A
is-hlevel (suc n) A = ∀ (a a' : A) → is-hlevel n (a ≡ a')

hfiber : {A B : Set}(f : A → B)(b : B) → Set
hfiber f b = Σ _ (λ a → f a ≡ b)

f-is-hlevel : (n : ℕ){A B : Set}(f : A → B) → Set
f-is-hlevel n f = ∀ b → is-hlevel n (hfiber f b)

proj₁-is-hlevel : (n : ℕ){A : Set}(B : A → Set)(is : ∀ a → is-hlevel n (B a)) → f-is-hlevel n (proj₁ {A = A} {B = B})
proj₁-is-hlevel n B is = {!!}

f-is-hlevel-from : (n : ℕ){A B : Set}(f : A → B) → is-hlevel n A → is-hlevel (suc n) B → f-is-hlevel n f
f-is-hlevel-from n f is1 is2 b = {!n!}

is-hlevel-Src : (n : ℕ){A B : Set}(f : A → B) → f-is-hlevel n f → is-hlevel n B →  is-hlevel n A
is-hlevel-Src n f is1 is2 = {!!}

f-contr : {A : Set}(B : A → Set) → (∀ a → isContr (B a)) → isContr (∀ a → B a)
f-contr B is = {!!}

impred : (n : ℕ){A : Set}(B : A → Set) → (∀ a → is-hlevel n (B a)) → is-hlevel n (∀ a → B a)
impred zero B is = f-contr B is
impred (suc n) B is = {!!}



isProp = is-hlevel 1

hProp = Σ Set isProp

prf : hProp → Set
prf = proj₁

uni : (A : hProp) → ∀{a b : prf A} → a ≡ b
uni A {a} {b} = proj₁ (proj₂ A a b)

isUni : (A : hProp) → ∀{a b : prf A}(p : a ≡ b) → p ≡ uni A
isUni A {a} {b} =  proj₂ (proj₂ A a b)

⊤ : hProp
⊤ = U.⊤ , (λ a a' → refl , (λ{refl → refl}))


⊥ : hProp
⊥ = E.⊥ , λ()


isofhlevelΣ : ∀(n : ℕ)(A  : Set)(B : A → Set)(is1 : is-hlevel n A) (is2 : ∀ a → is-hlevel n (B a)) → is-hlevel n (Σ A B)
isofhlevelΣ n A B is1 is2 = is-hlevel-Src n proj₁ (proj₁-is-hlevel n B is2) is1

sig-eq : {A : Set}{B : A → Set}
         {a b : A}(p : a ≡ b)
         {c : B a}{d : B b} →
         (subst (λ x → B x) p c ≡ d) →
         _≡_ {_} {Σ A B} (a , c) (b , d)
sig-eq refl refl = refl

{-
Σ' : (P : hProp)(Q : prf P → hProp) → hProp
Σ' P Q = ((Σ (prf P) (λ x → prf (Q x))) ,
         (λ{ (p1 , q1) (p2 , q2) → (sig-eq (uni P) (uni (Q p2))) , isofhlevelΣ {!!} (prf P) (λ x → prf (Q x)) {!isUni P!} {!!} ? }))
-}


∥_∥ : Set → Set₁
∥ X ∥ = (P : hProp) → (X → prf P) → prf P

∥_∥-isProp : ∀ X → isProp ∥ X ∥
∥_∥-isProp X = {!impred!}

ishinh : (A : Set) → hProp
ishinh A = ∥ A ∥ , ∥_∥-isProp _

h∃ : {A : Set}(B : A → hProp) → hProp
h∃ {A} B = ishinh (Σ A (λ a → prf (B a)))

{-
pair≡ : ∀{A B : Set}{a b : A}{c d : B} → a ≡ b → c ≡ d → (a , c) ≡ (b , d)
pair≡ refl refl = refl

_∧_ : hProp → hProp → hProp
(P , eq1) ∧ (Q , eq2) = (P × Q) , (λ{(p , q) (p1 , q1) → pair≡ (proj₁ (eq1 p p1)) (proj₁ (eq2 q q1)) , (λ eq3 → {!!})})
-}
\end{code}