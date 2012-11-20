\documentclass{article}

%agda literal file
\usepackage{agda}

\usepackage{dsfont}
\usepackage{amsthm}
\usepackage{color}
\usepackage{amsmath}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{autofe}

%customized package
\usepackage{mypack}

\begin{document}

\AgdaHide{
\begin{code}
module Definability where 

open import Data.Product
open import Algebra.FunctionProperties.Core
open import Data.Nat renaming (_+_ to _ℕ+_)

open import Relation.Binary.Core
open import Relation.Nullary
\end{code}
}

% Title
\title{Numbers, quotients, and definability of reals}

\author{Li Nuo}

%\date{June 07, 2012}

\maketitle

% TOC
%\tableofcontents

\section{Numbers}

Since Agda is known as a proof assistant, the library of numbers is
crucial. In such kind of proof assistants which are based on
Martin-L\"{o}f type theory , we need to construct the type of numbers and
the usual properties of them should be verifiable rather than
axiomatic.

There are different ways of defining numbers, even though they are
mathematically equivalent, they are technically different, which means
the proving of theorems about the numbers varies. For example,
integers can be defined by exploiting the isomorphism between $\Z$ and
$\N+\N$ :

\begin{code}

data ℤ : Set where
  -[1+_]    : (n : ℕ) → ℤ  -- -[1+ n ] stands for - (1 + n).
  +_           : (n : ℕ) → ℤ  -- + n stands for n.

\end{code}

And this is exactly the definition in Agda standard library version 0.6. This definition is easy to use since it has two cases and for each integer you have one unique representation. However intuitively we lose the "special position" held by 0. Of course we can define three cases definition with distinct 0 constructor but too many cases are not ideal for proving.

Alternatively we have another isomorphism between $\Z$ and
$\bigslant{\N\times\N}{\sim}$, namely constructing the set of integers
from quotienting the set of $\N\times\N$ by the following equivalence relation :

\begin{equation}
(n_1 , n_2) \sim (n_3 , n_4)\iff n_1 + n_4 = n_3 + n_2
\end{equation}
 
From this observation we can define a setoid implementation for integers.

\begin{code}


data ℤ₀ : Set where
  _,_ : ℕ → ℕ → ℤ₀

_∼_                               : Rel ℤ₀ _
(x1 , x2) ∼ (y1 , y2)   = (x1 ℕ+ y2) ≡ (y1 ℕ+ x2)

\end{code}
 The common operations defined on $\Z_0$($\bigslant{\N\times\N}{\sim}$) has only one case which are much simpler than the one for the previous definition,

\begin{code}

_+_ : ℤ₀ → ℤ₀ → ℤ₀
(x1 , x2) + (y1 , y2) = (x1 ℕ+ y1) , (x2 ℕ+ y2)

\end{code}
and we only need to prove that it respects the equivalence relation,

\begin{code}

_respects_ : {A : Set} → Op₂ A → Rel A _ → Set
_⊛_ respects _≈_ = ∀ a b c d → a ≈ b → c ≈ d → (a ⊛ c) ≈ (b ⊛ d)

\end{code}
Given two pairs equal setoid integers $(x , x₁) ∼ (x₂ , x₃)$ and $(x₄ , x₅) ∼ (x₆ , x₇)$, the goal just turns into some simple expression of natural numbers

$$x ℕ+ x₄ ℕ+ (x₃ ℕ+ x₇) ≡ x₂ ℕ+ x₆ ℕ+ (x₁ ℕ+ x₅)$$

which can be automatically solved in Agda (the detail looks cumbersome).

Given any operation respects the equivalence relation, we can easily
turns it into the corresponding operation for the set definition $\Z$
in a general way.

First, we need a normalization function to find the corresponding $z : \Z$ for any given $z_0 : \Z_0$.

\begin{code}

[_]                 : ℤ₀ → ℤ
[ m , 0 ]           = + m
[ 0 , suc n ]       = -[1+ n ]
[ suc m , suc n ]   = [ m , n ]

\end{code}

And the section of it

\begin{code}

⌜_⌝           : ℤ → ℤ₀
⌜ + n ⌝       = n , 0
⌜ -[1+ n ] ⌝  = 0 , suc n

\end{code}

Then the general lifting function is

\begin{code}

lift₂   : (_⊛_ : Op₂ ℤ₀)
        → Op₂ ℤ
lift₂ _⊛_ a b = [ ⌜ a ⌝ ⊛ ⌜ b ⌝ ]

\end{code}
 
Since we can prove the operation respects the equivalence relation, the lifted operation should have the same properties, which means we can also lift the proofs of the theorems on setoid integers.



%It better exploits the relationship between the set of
%natural numbers and the set of integers, because any integer is a
%result of subtracting two natural numbers which means we uniformly
%represent all integers, and the laws for basic operations are simpler
%to lifted from the ones for natural numbers.


In fact, this kind of relationship between setoids and sets can be generalized
as quotients. Given a setoid $(A,\sim)$, some set $ Q : Set $ can be seen as the corresponding quotient type over this setoid, if we have a function $  [ \cdot ] : A → Q $ such that it fulfils certain set of properties (details in \cite{aan}).

For the set rational numbers, we could also define it using setoids from the construction of fractions and the equivalence relation on fractions.

For real numbers, we could use cauchy sequences of rational numbers to represent them. However, we still can not find a way to define the set of reals in current setting of \itt{}.

From the obervations above, there is a pattern between different kinds of numbers, namely we can create a setoid using already defined number sets to represent a new number set. This kind of relation better exploits the relation between the number sets such that we can prove theorems much simpler.

\section{quotients}

The quotient type is unavailable in \itt{}, since it is extensional. 



\section{definability}







\bibliographystyle{plain}
\bibliography{my}
\end{document}