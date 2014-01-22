module Data.Rational.Normal where

open import Data.Rational as Rt
open import Data.Rational' as Rt₀ hiding (-_ ; _÷_ ; ∣_∣)

open import Data.Integer as ℤ using (∣_∣) renaming (-_ to ℤ-_)
open import Data.Integer' as ℤ' hiding (-_ ; suc ; [_] ; ∣_∣; _◃_ ; pred ; ⌜_⌝) renaming (p to ∣_∣')
import Data.Integer.Properties' as ℤ'
import Data.Integer.Setoid as ℤ₀
open import Data.Nat as ℕ renaming (_+_ to _ℕ+_ ; _*_ to _ℕ*_)
open import Data.Nat.GCD
open import Data.Nat.Divisibility using (_∣_ ; 1∣_ ; divides)
import Data.Nat.Coprimality as C
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Decidable

GCD′→ℚ : ∀ x y di → y ≢ 0 → C.GCD′ x y di → ℚ
GCD′→ℚ .(q₁ ℕ* di) .(q₂ ℕ* di) di neo (C.gcd-* q₁ q₂ c) = record { numerator = numr
          ; denominator-1 = pred q₂
          ; isCoprime = iscoprime }
   where
     numr = ℤ.+_ q₁
     deno = suc (pred q₂)
     
     numr≡q1 : ∣ numr ∣ ≡ q₁
     numr≡q1 = refl

     lzero : ∀ x y → x ≡ 0 → x ℕ* y ≡ 0
     lzero .0 y refl = refl

     q2≢0 : q₂ ≢ 0
     q2≢0 qe = neo (lzero q₂ di qe)

     invsuc : ∀ n → n ≢ 0 → suc (pred n) ≡ n
     invsuc zero nz with nz refl
     ... | ()
     invsuc (suc n) nz = refl
     
     deno≡q2 : deno ≡ q₂
     deno≡q2 = invsuc q₂ q2≢0
     
     transCop : ∀ {a b c d} → c ≡ a → d ≡ b → C.Coprime a b → C.Coprime c d
     transCop refl refl c = c

     copnd : C.Coprime ∣ numr ∣ deno
     copnd = transCop numr≡q1 deno≡q2 c

     witProp : ∀ a b → GCD a b 1 → True (C.coprime? a b)
     witProp a b gcd1 with gcd a b
     witProp a b gcd1 | zero , y with GCD.unique gcd1 y
     witProp a b gcd1 | zero , y | ()
     witProp a b gcd1 | suc zero , y = tt
     witProp a b gcd1 | suc (suc n) , y with GCD.unique gcd1 y
     witProp a b gcd1 | suc (suc n) , y | ()

     iscoprime : True (C.coprime? ∣ numr ∣ deno)
     iscoprime = witProp ∣ numr ∣ deno (C.coprime-gcd copnd)

-_ : ℚ → ℚ
-_ q = record { numerator = ℤ- numr
              ; denominator-1 = deno-1
              ; isCoprime = iscoprime- }
   where
     numr = ℚ.numerator q
     deno-1 = ℚ.denominator-1 q

     iscoprime : True (C.coprime? ∣ numr ∣ (suc deno-1))
     iscoprime = ℚ.isCoprime q

     forgetSign : ∀ x → ∣ x ∣ ≡ ∣  ℤ- x ∣
     forgetSign (ℤ.-[1+_] n) = refl
     forgetSign (ℤ.+_ zero) = refl
     forgetSign (ℤ.+_ (suc n)) = refl

     iscoprime- : True (C.coprime? ∣ ℤ- numr ∣ (suc deno-1))
     iscoprime- = subst (λ x → True (C.coprime? x (suc deno-1))) (forgetSign numr) iscoprime



[_] : ℚ₀ → ℚ
[ (+ 0) /suc d ] = ℤ.+_ 0 ÷ 1
[ (+ (suc n)) /suc d ] with gcd (suc n) (suc d)
[ (+ suc n) /suc d ] | di , g = GCD′→ℚ (suc n) (suc d) di (λ ()) (C.gcd-gcd′ g)

[ (-suc n) /suc d ] with gcd (suc n) (suc d)
... | di , g = - GCD′→ℚ (suc n) (suc d) di (λ ()) (C.gcd-gcd′ g)


ℤcon : ℤ.ℤ → ℤ
ℤcon (ℤ.-[1+_] n) = -suc n
ℤcon (ℤ.+_ n) = + n

⌜_⌝ : ℚ → ℚ₀
⌜ x ⌝ = (ℤcon (ℚ.numerator x)) /suc (ℚ.denominator-1 x)

{-

sound : ∀ {a b : ℚ₀} → a ∼ b → [ a ] ≡ [ b ]
sound {n /suc d} {n' /suc d'} eq = {!!}
-}
