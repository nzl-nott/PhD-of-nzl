\section{The design of this project}

The project consists of several parts catogorised by different kinds of numbers, integers, rational numbers, real numbers and complex numbers. For each part, there will be one or more alternative definitions. For each definition there are
several files containing the proofs of properties. The definition which is most convenient to use will be put in the primary file for each kind of numbers. The name convention and layout of code has been adapted to the standard library so that it is easy for add these codes into the standard library. User could import and make use of these numbers in a similar way as natural numbers. However, due to the existence of definitions of integers and rational numbers implemented by Nils Anders Danielsson, I have to change the name slightly to avoid ambiguity. I list the general definitions and properties I have done in this project below.

\subsection{Definition part}
\begin{enumerate}
\item \textit{Definition of numbers.} The definition should be placed at very first. For setoid definitions, a equivalence relation should be defined as well for examples,

\begin{code}
ℤ₀ = ℕ × ℕ

_∼_ : Rel ℤ₀
\end{code}

\item \textit{Ordering relations.} With the equivalence relation defined, we could prove the equality. Likewise, to enable Agda to prove unequality, we should define the unequality relations for numbers, or as the convention the ordering relations. For example,

\begin{code}
_≤_ : Rel ℤ₀

_<_ : Rel ℤ₀

_≥_ : Rel ℤ₀

_>_ : Rel ℤ₀
\end{code}

\item \textit{Sign functions.} There are negative numbers since integers. Therefore the sign function is necessary and useful in many proofs. For example,

a) decomposition

\begin{code}

sign          : ℤ → Sign

\end{code}

b) composition

\begin{code}

_◃_              : Sign → ℕ → ℤ

\end{code}

With the View "SignAbs",

\begin{code}
data SignAbs : ℤ → Set where
  _◂_ : (s : Sign) (n : ℕ) → SignAbs (s ◃ n)

signAbs : ∀ m → SignAbs m
signAbs m = subst SignAbs (sign◃ m) (sign m ◂ (p m))
\end{code}

we could use pattern match to decompose an integer to be a sign and a natural number.

\item \textit{Abbreviation of conditions.} We often need these conditions in theorem proving. There are two advantages, first it makes the conditions consistent, second we do not need to unfold the definition since we can give the whole number to conditions. For example,

\begin{code}

is0   : ℤ₀ → Set
is0 (a , b) = a ≡ b

¬0   : ℤ₀ → Set
¬0 (a , b) = a ≢ b

is+ : ℤ₀ → Set
is+ (a , b) = b ℕ< a

is- : ℤ₀ → Set
is- (a , b) = a ℕ< b

\end{code}

\item \textit{Conversion functions.} We need to convert the current number to other type of number so that we can deal with the computation mixed with different types of numbers. For example,

a) p - projection: absolute value but type is ℕ

\begin{code}

projection : ℤ₀ → ℕ

\end{code}

b) i - injection: a representative ℤ₀ for ℕ $(ℕ ⊂ ℤ)$

\begin{code}

injection : ℕ → ℤ₀

\end{code}

\item \textit{Arithmetic.} Then we should define the operations. Most definitions in this project do not have mixed types. There are two main kinds of elementary operations, unary and binary operations, For example,

a) Successor

\begin{code}

suc          : Op₁ ℤ₀

\end{code}

b) Predecessor

\begin{code}

pred         : Op₁ ℤ₀

\end{code}

c) Negation : $- (3 - 2) = 2 - 3$

\begin{code}

-_  : Op₁ ℤ₀

\end{code}

d) Absolute value : ℤ₀

\begin{code}

∣_∣ : Op₁ ℤ₀

\end{code}

e) Addition : $ (a - b) + (c - d) = (a + c) - (b + d) $

\begin{code}

_+_ : Op₂ ℤ₀

\end{code}

f) Minus : (a - b) - (c - d) = (a + d) - (b + c)

\begin{code}

_-_ : Op₂ ℤ₀

\end{code}

g) Multiplication:
  (x - y) * (m - n) = (x * m + y * n) - (x * n + y * m ))

\begin{code}

_*_ : Op₂ ℤ₀

\end{code}

There are also operations with mixed types,

\begin{code}

_ℕ*ℤ₀_ : ℕ → ℤ₀ → ℤ₀
n ℕ*ℤ₀ (z+ , z-) = n ℕ* z+ , n ℕ* z-

\end{code}

For rational numbers, there are more operations to be defined,

Inverse function: It does not define on zero.

\begin{code}

inverse       : (q : ℚ₀) → {p : ¬0 q} → ℚ₀

\end{code}

Division: We can define the division for ℚ₀ because the results of division of ℕ or ℤ and ℚ₀ are always ℚ₀

\begin{code}

_÷_         : (a b : ℚ₀) → {p : ¬0 b} → ℚ₀

\end{code}

\end{enumerate}

For the power functions, as we have to use fractional forms, and even real numbers for the root functions, which is the reverse of power functions, I defined some of them in a separate files called "Power" which is defined after the rational numbers.


\subsection{Properties part}

Due to the inefficiency problem arose from too much code in one file, I separate the proofs of properties into several parts. The general catogorising approach of these properties are separate into three parts, basic properties which includes the basic properties which are essential for the second part which includes all the properties to form a commutative ring for integers or form a field for rational numbers. Finally, the advanced part contains some properties which can be proved after we proved the second part and usually include some lemmas for theorems of the higher level numbers.

\subparagraph{Basic properties.} In the basic the common properties are:

\begin{enumerate}
\item \textit{some relations and conditions are decidable.} For example,

\begin{code}

_≟_   : Decidable _≡_

0?   : ∀ z → Dec (is0 z)

¬0? : ∀ z → Dec (¬0 z)

is+? : ∀ z → Dec (is+ z)

_≤?_ : Decidable _≤_

\end{code}

\item \textit{$(Num, = , \leq)$ forms a total order.} For example,

\begin{code}

decTotalOrder : DecTotalOrder
decTotalOrder = record
  { Carrier         = ℤ
  ; _≈_             = _≡_
  ; _≤_             = _≤_
  ; isDecTotalOrder = record
      { isTotalOrder = record
          { isPartialOrder = record
              { isPreorder = record
                  { isEquivalence = isEquivalence
                  ; reflexive     = refl′
                  ; trans         = trans
                  ; ∼-resp-≈      = resp₂ _≤_
                  }
              ; antisym  = antisym
              }
          ; total = total
          }
      ; _≟_  = _≟_
      ; _≤?_ = _≤?_
      }
  }
\end{code}

\item \textit{some other properties for ordering functions.} For example,

+ preserves ≤

\begin{code}
+-pres₂′ : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
\end{code}

+ cancellation for ≤ 

\begin{code}

+-cancel′ : ∀ a {b c} → a + b ≤ a + c → b ≤ c
+-cancel′ a = ℤ₀.+l-cancel′ ⌜ a ⌝ ∘ +compl≤

\end{code}

Also the properties to form a setoid we mentioned before is also included in this file. The three basic thoerems which proves the equivalence relations, namely "reflexivity", "symmetry" and "transitivity" are widely used.

\end{enumerate}

\subparagraph{Commutative Ring (or Field)} In the second part, there are a lot of axioms for operations which we used a lot in computations. For example,

\begin{enumerate}
\item the identity of $+$ : $0 + z = z$ and $z + 0 = z$

\begin{code}

+-identity : Identity (+ 0) _+_
+-identity = 0+z≡z , z+0≡z

\end{code}

\item The Commutativity of $+$: $m * n = n * m$

\begin{code}

+-comm : Commutative _+_

\end{code}

\item The Associativity of $+$: $(a + b) + c = a + (b + c)$
\begin{code}
+-assoc : Associative _+_
\end{code}

\item $-\_$ is inverse:
$x + (- x) = 0$ and
$(- x) + x = 0$

\begin{code}

+-inverse : Inverse (+ 0) -_ _+_
+-inverse = +-leftInverse , +-rightInverse

\end{code}

\item zero times any number is still zero:

$0 * z = 0$


$z * 0 = 0$
\begin{code}
*-zero : Zero  (+ 0) _*_
*-zero = 0*z≡0 , z*0≡0

\end{code}

\item The distributivity of $+$ and $*$ :

$a * (b + c) = a * b + a * c$

$(b + c) * a = b * a + c * a$

\begin{code}

distrib-*-+ : _*_ DistributesOver _+_
distrib-*-+ = distˡ , distʳ

\end{code} 

\end{enumerate}

There are more properties than which are similar to these and finally they could form a ring or even a field. for example,
\begin{code}

commutativeRing : CommutativeRing
commutativeRing = record
  { _+_                   = _+_
  ; _*_                   = _*_
  ; -_                    = -_
  ; 0#                    = (+ 0)
  ; 1#                    = (+ 1)
  ; isCommutativeRing = isCommutativeRing
  }

\end{code}

With commutative ring we could build the ring solver which is an automatic prover and solver for simple propositions.

\begin{code}

import Algebra.RingSolver.Simple as Solver
import Algebra.RingSolver.AlmostCommutativeRing as ACR
module RingSolver =
  Solver (ACR.fromCommutativeRing commutativeRing)

\end{code}


\subparagraph{Advanced Properties}The advanced properties part imports the second part so that some more advanced properties can be proved easier after we have the theorems proved before.

\begin{enumerate}

\item Integrity. The Integerity is the name for properties and it is also called mulitiplication cancellation fucntions. We need a non-zero condition for the cancelled term. For example,

\begin{code}
l-integrity : ∀ {m n} a → (p : ¬0 a) → a * m ≡ a * n → m ≡ n
\end{code}

\item $*$ preserves $≤$, if n is non-negative in $a ≤ b → n * a ≤ n * b$

\begin{code}

*-pres′ : ∀ {a b} n → a ≤ b → (n , 0) * a ≤ (n , 0) * b
 
\end{code}

\item Solve an equation: if $m * n ∼ 0$ and m is not 0 then n must be 0

\begin{code}

solve0 : ∀ m {n} → (p : ¬0 m) → m * n ≡ + 0 → n ≡ + 0

solve0' : ∀ m {n} → (p : ¬0 m) → n * m ≡ + 0 → n ≡ + 0

\end{code}

\item To simplfy some common actions to exchange the positions of some elements in polynomials when construct proof manually rather than using ring solvers, there is a set of exchange functions defined here. For example,

\begin{code}

*-ex₁ : ∀ a b c → a * (b * c) ≡ c * (b * a)

*-exchange₁ : ∀ a b c d → (a * b) * (c * d) ≡ (a * d) * (c * b)

*-exchange₂ : ∀ a b c d → (a * b) * (c * d) ≡ (c * b) * (a * d)

\end{code}

\end{enumerate}

Besides these, when I need a lemma that seems useful generally or easier to prove in current number environment, I will also prove it in this part. For example,

\begin{code}
*+-simp : ∀ a b → (+ a) * (+ b) ≡ + (a ℕ* b)

-*cong : ∀ m n → m * n ≡ (- m) * (- n)
\end{code}

\subparagraph{Properties combined} After all, a single file called "Properties" which combine all the properties is necessary to provide a easy access to all these properties. For example,

\begin{code}
module Data.Integer.Properties where

open import Data.Integer.Properties.BasicProp public
open import Data.Integer.Properties.CommutativeRing public
open import Data.Integer.Properties.AdvancedProp public

\end{code}

It is also a better way to manage what properties to put in the whole properties file. After that we can add a set of properties without affecting the rest of properties if we put all properties in one single file.

