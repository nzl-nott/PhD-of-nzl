module nuo where

open import Relation.Binary.PropositionalEquality
open import Data.Nat

postulate ext : {A B : Set}{f g : A → B} → 
                ((a : A) → f a ≡ g a) → f ≡ g

id : ℕ → ℕ
id n = n

+0 : ℕ → ℕ
+0 n = n + 0

+0lem : (n : ℕ) → n ≡ n + 0
+0lem zero = refl
+0lem (suc n) = cong suc (+0lem n)

lem : id ≡ +0
lem = ext +0lem

P : (ℕ → ℕ) → Set
P f = ℕ

seven : ℕ
seven = 7

lem2 : {f g : ℕ → ℕ} → (p : f ≡ g) → (n : ℕ) → n ≡ subst P p n
lem2 refl n = refl

seven' : ℕ
seven' = subst P lem 7

uip : {A B : Set} → {a b : A → B} → (p q : a ≡ b) → p ≡ q
uip refl refl = refl

exercise : seven ≡ seven'
exercise = lem2 lem 7