--------------------------------------------------

Integer

--------------------------------------------------
\begin{code}

module Data.Integer' where

open import Data.Bool
open import Algebra.FunctionProperties.Core
open import Data.Sign as Sign using (Sign)
  renaming (_*_ to _S*_)
open import Data.Product
open import Data.Nat using (ℕ; zero) renaming (suc to nsuc; pred to npre)
open import Data.Integer.Setoid as ℤ₀ using (ℤ₀ ; _∼_ ; _,_; zrefl ; zsym ; _>∼<_ ; _∼_isEquivalence)
  renaming (_+_ to _ℤ₀+_ ; _-_ to _ℤ₀-_ ; _*_ to _ℤ₀*_ ;
  _≤_ to _ℤ₀≤_; _<_ to _ℤ₀<_)
import Data.Integer.Setoid.Properties as ℤ₀
  using (refl') 
  renaming (_≟_ to _ℤ₀≟_ ; _≤?_ to _ℤ₀≤?_)
open import Relation.Binary.Core
open import Symbols
open import Data.Nat.Properties+ as ℕ using (_+suc_≢0_)
open import Relation.Binary.PropositionalEquality hiding ([_])

infixl 7 _*_
infixl 6 _+_ _-_
infix 4 _≤_ _<_ _≥_ _>_

\end{code}

1. Definition of ℤ

\begin{code}

data ℤ : Set where
  +_    : (n : ℕ) → ℤ
  -suc_ : (n : ℕ) → ℤ

\end{code}

There are two ways to construct ℤ, both constructors use natural numbers. +_ maps natural numbers to [0 ∼ +∞) and -suc maps natural numbers to [-1 ∼ -∞).

2. Normalisation

a) normalise the setoid integer to normal form e.g. (3 , 2) → + 1

\begin{code}

[_]                   : ℤ₀ → ℤ
[ m , 0 ]             = + m
[ 0 , nsuc n ]       = -suc n
[ nsuc m , nsuc n ] = [ m , n ]

\end{code}

To prove it is a normalisation, we need to find an inverse function of it.

b) denormalise the normal integer to one representative setoid integer e.g. + 1 → (3 , 2) ∼ [(1 , 0)]₌
(type using \c with left ⌜ and right ⌝)

\begin{code}

⌜_⌝        : ℤ → ℤ₀
⌜ + n ⌝    = n , 0
⌜ -suc n ⌝ = 0 , ℕ.suc n


\end{code}


These two functions are quite important in the mechanism between ℤ and ℤ₀. They map one to the other so that we could define all the functions of ℤ from the ones of the ℤ₀. The situation looks similar as before (ℤ₀ and ℕ), but requires some auxiliary functions to eliminate these two functions.

\end{code}

3. Ordering

\begin{code}

_≤_   : Rel ℤ _
m ≤ n = ⌜ m ⌝ ℤ₀≤ ⌜ n ⌝

_<_ : Rel ℤ _
m < n = ⌜ m ⌝ ℤ₀< ⌜ n ⌝

_≥_ : Rel ℤ _
m ≥ n = n ≤ m

_>_ : Rel ℤ _
m > n = n < m

\end{code}

4. Sign

a) decomposition
Gives the sign. For zero the sign is arbitrarily chosen to be +.

\begin{code}

sign          : ℤ → Sign
sign (+ n)    = Sign.+
sign (-suc n) = Sign.-

\end{code}

b) composition

\begin{code}

infix 5 _◃_

_◃_              : Sign → ℕ → ℤ
Sign.+ ◃ n       = + n
Sign.- ◃ zero  = + 0
Sign.- ◃ nsuc n = -suc n

\end{code}

5. Conversion with ℕ

a) projection

\begin{code}

p          : ℤ → ℕ
p (+ n)    = n
p (-suc n) = ℕ.suc n

\end{code}

b) injection

\begin{code}

i : ℕ → ℤ
i = +_

\end{code}

c) ℕ to positive ℤ

\begin{code}

+suc : ℕ → ℤ
+suc n = + ℕ.suc n

\end{code}

6. Abbreviation for some conditions

\begin{code}

is0        : ℤ → Set
is0 z      = z ≡ + 0

¬0     : ℤ → Set
¬0 z   = z ≢ + 0

is+   : ℤ → Set
is+ z = ∃ λ n → z ≡ + ℕ.suc n

\end{code}

7. Operators

a)  Generalisation of operators (lifting operators):
the generalisation of the conversion from the operators for the ℤ₀ to the ones for the ℤ

\begin{code}

Op : ℕ → (A : Set) → Set
Op 0 A = A
Op (nsuc n) A = A → Op n A

liftOp : ∀ n → Op n ℤ₀ → Op n ℤ
liftOp 0 op = [ op ]
liftOp (nsuc n) op = λ x → liftOp n (op ⌜ x ⌝)

\end{code}

However this liftOp is unsafe

\begin{code} 

Cong1 : Op 1 ℤ₀ → Set
Cong1 f = ∀ {a b} → a ∼ b → f a ∼ f b

Cong2 : Op 2 ℤ₀ → Set
Cong2 op = ∀ {a b c d} → a ∼ b → c ∼ d → op a c ∼ op b d

liftOp1safe : (f : Op 1 ℤ₀) → Cong1 f → Op₁ ℤ
liftOp1safe f cong = λ n → [ f ⌜ n ⌝ ]

liftOp2safe      : (op : Op 2 ℤ₀) → Cong2 op → Op₂ ℤ
liftOp2safe _op_ cong = λ m n → [ ⌜ m ⌝ op ⌜ n ⌝ ]



\end{code}

b) negation

\begin{code}

-_ : Op 1 ℤ
-_ = liftOp 1 ℤ₀.-_

\end{code}

c) absolute value

\begin{code}

∣_∣          : Op₁ ℤ
∣ + n ∣      = + n
∣ -suc n ∣ = + ℕ.suc n

\end{code}

d) successor

\begin{code}

suc : Op₁ ℤ
suc (+ n)          = + nsuc n
suc (-suc 0)       = + 0
suc (-suc (nsuc n)) = -suc n

\end{code}

e) predecessor

\begin{code}

pred : Op₁ ℤ
pred (+ zero)  = -suc zero
pred (+ nsuc n) = + n
pred (-suc n)    = -suc nsuc n

\end{code}

f) addition

\begin{code}

_+_ : Op₂ ℤ
_+_ = liftOp 2 _ℤ₀+_

\end{code}

g) minus

\begin{code}

_-_ : Op₂ ℤ
_-_ = liftOp 2 _ℤ₀-_

\end{code}

h) multiplication

\begin{code}

_*_   : Op₂ ℤ
_*_  = liftOp 2 _ℤ₀*_

\end{code}


\begin{code}

GE : ℤ → ℤ → Bool
GE a b = ℤ₀.GE ⌜ a ⌝ ⌜ b ⌝


\end{code}