--------------------------------------------------

Integer (setoid)

--------------------------------------------------

\begin{code}
module Data.Integer.Setoid where

-- open import Data.Product using (∃! ; _,_)
open import Data.Bool
open import Function using (_$_ ; _∘_)
open import Algebra.FunctionProperties.Core
open import Function using (_∘_)
open import Data.Nat as ℕ using (zero ; ℕ ; suc ; pred)
  renaming (_≟_ to _ℕ≟_ ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ;
            _≤_ to _ℕ≤_; _<_ to _ℕ<_)
open import Data.Nat.Properties
open import Data.Nat.Properties+
open import Data.Sign hiding (_*_)
open import Relation.Nullary
open import Relation.Binary

open import Symbols

open import Relation.Binary.PropositionalEquality as PE hiding ([_])

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

_∼_ : Rel ℤ₀ _
(x+ , x-) ∼ (y+ , y-) = (x+ ℕ+ y-) ≡ (y+ ℕ+ x-)
\end{code}

The '∼' is equivalence

a) reflexivity: ∀ a → a ∼ a

\begin{code}

zrefl : Reflexive _∼_
zrefl {x+ , x-} = refl

\end{code}

b) symmetry: ∀ a b → a ∼ b → b ∼ a

\begin{code}

zsym : Symmetric _∼_
zsym {x+ , x-} {y+ , y-} = sym

\end{code}

c) transitivity:  ∀ a b c → a ∼ b /\ b ∼ c → a ∼ c
(the symbol is easier for use)

\begin{code}

infixl 40 _>∼<_

_>∼<_ : Transitive _∼_
_>∼<_ {x+ , x-} {y+ , y-} {z+ , z-} x=y y=z = cancel-+-left (y+ ℕ+ y-) $ swap24 y+ y- x+ z- >≡< ((y=z += x=y) >≡< swap13 z+ y- y+ x-)


\end{code}

d) Combine these 3 propertiese we can prove that '∼' is equivalence

\begin{code}

_∼_isEquivalence : IsEquivalence _∼_
_∼_isEquivalence = record
  { refl  = zrefl
  ; sym   = zsym
  ; trans = _>∼<_
  }

\end{code}

(ℤ₀, ∼) is a setoid

\begin{code}

ℤ-Setoid : Setoid _ _
ℤ-Setoid = record
  { Carrier       = ℤ₀
  ; _≈_           = _∼_
  ; isEquivalence = _∼_isEquivalence
  }

\end{code}

normalisation with respect to the equivalence relation

\begin{code}

[_]                   : ℤ₀ → ℤ₀
[ m , 0 ]             = m , 0
[ 0 , suc n ]       = 0 , suc n
[ suc m , suc n ] = [ m , n ]

normal-1-step : ∀ a {b} → (suc a , suc b) ∼ (a , b)
normal-1-step = sm+n≡m+sn

normal-sound : ∀ a → [ a ] ∼ a
normal-sound (_ , 0) = refl
normal-sound (0 , suc n) = refl
normal-sound (suc a , suc b) = normal-sound (a , b) >∼< ⟨ normal-1-step a ⟩ 

nm-lem : ∀ n n' → suc (n ℕ+ 0) ≡ suc (n' ℕ+ 0) → n ≡ n'
nm-lem n n' eq = +r-cancel 0 (cong pred eq)

nu' : ∀ a → [ [ a ] ] ≡ [ a ]
nu' (x , ℕ.zero) = refl
nu' (ℕ.zero , suc x₁) = refl
nu' (suc x , suc x₁) = nu' (x , x₁)


normal-unique : ∀ a b → a ∼ b → [ a ] ≡ [ b ]
normal-unique (zero , a') (zero , .a') refl = refl
normal-unique (zero , a') (suc n , zero) ()
normal-unique (zero , a') (suc n , suc n') eq = normal-unique (zero , a') (n , n') (cong pred eq)
normal-unique (suc n , zero) (zero , b') ()
normal-unique (suc n , zero) (suc n' , zero) eq with nm-lem n n' eq
normal-unique (suc .n' , zero) (suc n' , zero) eq | refl = refl
normal-unique (suc n , zero) (suc n' , suc n0) eq = normal-unique (suc n , zero) (n' , n0) (sm+n≡m+sn n >≡< cong pred eq)
normal-unique (suc n , suc n') b eq = normal-unique (n , n') b (⟨ sm+n≡m+sn n ⟩ >∼< eq)


\end{code}

2. Ordering

\begin{code}

infix 4 _≤_ _<_ _≥_ _>_

_≤_ : Rel ℤ₀ _
(x+ , x-) ≤ (y+ , y-) = (x+ ℕ+ y-) ℕ≤ (y+ ℕ+ x-)

_<_ : Rel ℤ₀ _
(x+ , x-) < (y+ , y-) = (x+ ℕ+ y-) ℕ< y+ ℕ+ x-

_≥_ : Rel ℤ₀ _
m ≥ n = n ≤ m

_>_ : Rel ℤ₀ _
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