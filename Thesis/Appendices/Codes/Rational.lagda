\AgdaHide{
\begin{code}

module Rational where

import Data.Rational as Rt
-- open import Data.Rational' as Rt₀ hiding (-_ ; _÷_ ; ∣_∣)
open import Data.Product
open import Data.Integer hiding (suc; pred) renaming (-[1+_] to -suc_; _*_ to _ℤ*_;-_ to ℤ-_)
open import QInteger  hiding (_∼_; [_]; ⌜_⌝; sound ; stable) -- as ℤ' hiding (-_ ; suc ; [_] ; ∣_∣; _◃_ ; pred ; ⌜_⌝) renaming (p to ∣_∣')
-- import Data.Integer.Properties' as ℤ'
-- import Data.Integer.Setoid as ℤ₀
open import Data.Nat as ℕ renaming (_+_ to _ℕ+_ ; _*_ to _ℕ*_)
open import Data.Nat.GCD
open import Data.Nat.Divisibility using (_∣_ ; 1∣_ ; divides)
open import Data.Nat.Coprimality
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Decidable
\end{code}
}

\section{Rational numbers}

\begin{code}
data ℚ₀ : Set where
  _/suc_ : (n : ℤ) → (d : ℕ) → ℚ₀
\end{code}

\textbf{Extractions}

\begin{code}
num : ℚ₀ → ℤ
num (n /suc _) = n

den : ℚ₀ → ℕ
den (_ /suc d) = suc d
\end{code}

\textbf{Equivalence relation}

\begin{code}
infixl 2 _∼_

_∼_   : ℚ₀ → ℚ₀ → Set
n1 /suc d1 ∼ n2 /suc d2 =  n1 ℤ* (+ suc d2) ≡ n2 ℤ* (+ suc d1)
\end{code}

Property: a fraction is reduced

i.e. the absolute value of the numerator is comprime to the denominator

\begin{code}
IsReduced : ℚ₀ → Set
IsReduced (n /suc d) = True (coprime? ∣ n ∣ (suc d))
\end{code}

The Definition of $\Q$ which is equivalent to the one in standard library

\begin{code}
ℚ : Set
ℚ = Σ[ q ∶ ℚ₀ ] IsReduced q
\end{code}

\textbf{Normalisation function}:

1. Calculate a reduced fraction for $\frac{x}{y}$ with a condition that y is not zero.

\begin{code}
calℚ : ∀(x y : ℕ) → y ≢ 0 → ℚ
calℚ x y neo with gcd′ x y
calℚ .(q₁ ℕ* di) .(q₂ ℕ* di) neo 
  | di , gcd-* q₁ q₂ c = (numr /suc pred q₂) , iscoprime
   where
     numr = + q₁
     deno = suc (pred q₂)

     lzero : ∀ x y → x ≡ 0 → x ℕ* y ≡ 0
     lzero .0 y refl = refl

     q2≢0 : q₂ ≢ 0
     q2≢0 qe = neo (lzero q₂ di qe)

     invsuc : ∀ n → n ≢ 0 → n ≡ suc (pred n)
     invsuc zero nz with nz refl
     ... | ()
     invsuc (suc n) nz = refl
     
     deno≡q2 : q₂ ≡ deno
     deno≡q2 = invsuc q₂ q2≢0

     copnd : Coprime q₁ deno
     copnd = subst (λ x → Coprime q₁ x) deno≡q2 c

     witProp : ∀ a b → GCD a b 1 
             → True (coprime? a b)
     witProp a b gcd1 with gcd a b
     witProp a b gcd1 | zero , y with GCD.unique gcd1 y
     witProp a b gcd1 | zero , y | ()
     witProp a b gcd1 | suc zero , y = tt
     witProp a b gcd1 | suc (suc n) , y 
                                 with GCD.unique gcd1 y
     witProp a b gcd1 | suc (suc n) , y | ()

     iscoprime : True (coprime? ∣ numr ∣ deno)
     iscoprime = witProp _ _ (coprime-gcd copnd)
\end{code}

2.Negation

\begin{code}
-_ : ℚ → ℚ
-_ ((n /suc d) , isC) = ((ℤ- n) /suc d) ,
   subst (λ x → True (coprime? x (suc d))) 
     (forgetSign n) isC
   where
     forgetSign : ∀ x → ∣ x ∣ ≡ ∣  ℤ- x ∣
     forgetSign (-suc n) = refl
     forgetSign (+ zero) = refl
     forgetSign (+ (suc n)) = refl
\end{code}

3.Normalisation function

\begin{code}
[_] : ℚ₀ → ℚ
[ (+ n) /suc d ] = calℚ n (suc d) (λ ())
[ (-suc n) /suc d ] = - calℚ (suc n) (suc d) (λ ())
\end{code}

Embedding function

\begin{code}
⌜_⌝ : ℚ → ℚ₀
⌜_⌝ = proj₁
\end{code}


\AgdaHide{
\begin{code}
{-
GCD′→ℚ : ∀ x y di → y ≢ 0 → C.GCD′ x y di → ℚ
GCD′→ℚ .(q₁ ℕ* di) .(q₂ ℕ* di) di neo (C.gcd-* q₁ q₂ c) 
  = record { numerator = numr
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
     
     transCop : ∀ {a b c d} → c ≡ a → d ≡ b 
              → C.Coprime a b → C.Coprime c d
     transCop refl refl c = c

     copnd : C.Coprime ∣ numr ∣ deno
     copnd = transCop numr≡q1 deno≡q2 c

     witProp : ∀ a b → GCD a b 1 
             → True (C.coprime? a b)
     witProp a b gcd1 with gcd a b
     witProp a b gcd1 | zero , y with GCD.unique gcd1 y
     witProp a b gcd1 | zero , y | ()
     witProp a b gcd1 | suc zero , y = tt
     witProp a b gcd1 | suc (suc n) , y 
                                 with GCD.unique gcd1 y
     witProp a b gcd1 | suc (suc n) , y | ()

     iscoprime : True (C.coprime? ∣ numr ∣ deno)
     iscoprime = witProp ∣ numr ∣ deno 
                 (C.coprime-gcd copnd)
\end{code}

2.Negation

\begin{code}
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
     forgetSign (-suc n) = refl
     forgetSign (+ zero) = refl
     forgetSign (+ (suc n)) = refl

     iscoprime- : True (C.coprime? ∣ ℤ- numr ∣ (suc deno-1))
     iscoprime- = subst (λ x → True (C.coprime? x (suc deno-1))) 
                  (forgetSign numr) iscoprime
\end{code}

3.Normalisation function

\begin{code}
[_] : ℚ₀ → ℚ
[ (+ 0) /suc d ] = ℤ.+_ 0 ÷ 1

[ (+ (suc n)) /suc d ] with gcd (suc n) (suc d)

[ (+ suc n) /suc d ] | di , g = GCD′→ℚ (suc n) (suc d) 
                              di (λ ()) (C.gcd-gcd′ g)

[ (-suc n) /suc d ] with gcd (suc n) (suc d)
... | di , g = - GCD′→ℚ (suc n) (suc d) di (λ ()) 
             (C.gcd-gcd′ g)
\end{code}

Embedding function

\begin{code}
⌜_⌝ : ℚ → ℚ₀
⌜ q ⌝ = (ℚ.numerator q) /suc (ℚ.denominator-1 q)
-}
\end{code}

}