--------------------------------------------------

Integer (setoid)

--------------------------------------------------

\begin{code}
module Data.Integer.Setoid where

open import Data.Bool
open import Algebra.FunctionProperties.Core
open import Function using (_∘_)
open import Data.Nat as ℕ using (ℕ ; suc)
  renaming (_≟_ to _ℕ≟_ ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ;
            _≤_ to _ℕ≤_; _<_ to _ℕ<_)
open import Data.Sign hiding (_*_)
open import Level using (zero)
open import Relation.Binary.Core
open import Relation.Nullary

\end{code}

1. Definition

a. Integers can be defined as pairs of natural numbers:
   (x₊ , x₋) represents (x₊ - x₋) e.g. (3 , 2) = (11 , 10) = [(1,0)]₌

\begin{code}

infix 4 _,_

data ℤ₀ : Set where
  _,_ : ℕ → ℕ → ℤ₀

proj₁ : ℤ₀ → ℕ
proj₁ (a , _) = a

proj₂ : ℤ₀ → ℕ
proj₂ (_ , b) = b

\end{code}

b. An equivalence relation is part of a setoid of definition:

\begin{code}

infixl 2 _∼_

_∼_ : Rel ℤ₀ zero
(x+ , x-) ∼ (y+ , y-) = (x+ ℕ+ y-) ≡ (y+ ℕ+ x-)


[_]                   : ℤ₀ → ℤ₀
[ m , 0 ]             = m , 0
[ 0 , suc n ]       = 0 , suc n
[ suc m , suc n ] = [ m , n ]
\end{code}

2. Ordering

\begin{code}

infix 4 _≤_ _<_ _≥_ _>_

_≤_ : Rel ℤ₀ zero
(x+ , x-) ≤ (y+ , y-) = (x+ ℕ+ y-) ℕ≤ (y+ ℕ+ x-)

_<_ : Rel ℤ₀ zero
(x+ , x-) < (y+ , y-) = (x+ ℕ+ y-) ℕ< y+ ℕ+ x-

_≥_ : Rel ℤ₀ zero
m ≥ n = n ≤ m

_>_ : Rel ℤ₀ zero
m > n = n < m

\end{code}

3. Sign

a) decomposition

\begin{code}

sign                 : ℤ₀ → Sign
sign (0 , _)         = -
sign (suc m , suc n) = sign (m , n)
sign (_ , _)         = +

\end{code}

b) composition

\begin{code}

_◃_         : Sign → ℕ → ℤ₀
_ ◃ ℕ.zero  = 0 , 0
- ◃ suc n   = 0 , suc n
+ ◃ suc n   = suc n , 0

\end{code}

4. Abbreviation for some widely-used conditions
   (There is no need to unfold the definition)

\begin{code}

is0   : ℤ₀ → Set
is0 (a , b) = a ≡ b

¬0   : ℤ₀ → Set
¬0 z = ¬ (is0 z)

is+ : ℤ₀ → Set
is+ (a , b) = b ℕ< a

is- : ℤ₀ → Set
is- (a , b) = a ℕ< b

\end{code}

5. Conversion

a) p - projection: absolute value but type is ℕ

\begin{code}

p                 : ℤ₀ → ℕ
p (m , 0)         = m
p (0 , n)         = n
p (suc m , suc n) = p (m , n)

\end{code}

b) i - injection: a representative ℤ₀ for ℕ (ℕ ⊂ ℤ)

\begin{code}

i   : ℕ → ℤ₀
i n = n , 0

\end{code}

6. Arithmetic

a) successor

\begin{code}

zsuc          : Op₁ ℤ₀
zsuc (m , n)  = suc m , n

\end{code}

b) predecessor

\begin{code}

zpre         : Op₁ ℤ₀
zpre (m , n) = m , suc n

\end{code}

c) negation : - (3 - 2) = 2 - 3

\begin{code}

-_  : Op₁ ℤ₀
- (x , y)  = (y , x)

\end{code}

d) absolute value : ℤ₀

\begin{code}

∣_∣ : Op₁ ℤ₀
∣_∣ = i ∘ p

\end{code}

e) addition : (a - b) + (c - d) = (a + c) - (b + d)

\begin{code}

infixl 6 _+_ _-_

_+_ : Op₂ ℤ₀
(x+ , x-) + (y+ , y-) = (x+ ℕ+ y+) , (x- ℕ+ y-)

\end{code}

f) minus : (a - b) - (c - d) = (a + d) - (b + c)

\begin{code}

_-_ : Op₂ ℤ₀
(x+ , x-) - (y+ , y-) = (x+ ℕ+ y-) , (x- ℕ+ y+)

\end{code}

g) multiplication:
  (x - y) * (m - n) = (x * m + y * n) - (x * n + y * m ))

\begin{code}

infixl 7 _*_

_*_ : Op₂ ℤ₀
(x+ , x-) * (y+ , y-) = (x+ ℕ* y+ ℕ+ x- ℕ* y-) , (x+ ℕ* y- ℕ+ x- ℕ* y+)

\end{code}


These are the operators for ℤ₀. Most of them are defined on the operation on ℕ, the benefit of this is in the proving of properties. You will see how it ease the way of proving properties of ℤ₀.
I did not define the division because the result of division could be not integer . To do division, it should first be converted to rational numbers, then doing the division, and the result will be rational number.


i) ℕ * ℤ₀ : n * (a - b) = n * a - n * b

n ℕ*ℤ₀ x = i n * x this is the primary definition
But if we unfold the definition, we could found it only has some extra parts such as n * 0 or 0 * n which we know are redundant from the properties of ℕ, so that we can simplify it and the result is the first definition below

Note: The proof that they are equivalent is in the latter part

\begin{code}

_ℕ*ℤ₀_ : ℕ → ℤ₀ → ℤ₀
n ℕ*ℤ₀ (z+ , z-) = n ℕ* z+ , n ℕ* z-


_ℕ*ℤ₀'_   : ℕ → ℤ₀ → ℤ₀
n ℕ*ℤ₀' z = i n * z

-- Greater or equal?


ℕGE : ℕ → ℕ → Bool
ℕGE 0 0 = true
ℕGE 0 (suc n) = false
ℕGE (suc n) 0 = true
ℕGE (suc n) (suc n') = ℕGE n n'

GE : ℤ₀ → ℤ₀ → Bool
GE (a , a') (b , b') = ℕGE (a ℕ+ b') (b ℕ+ a')

\end{code}