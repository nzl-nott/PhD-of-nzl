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
module SetoidNumbers where 

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

\section{Introduction}



There are several number systems, $\N$, $\Z$, $\Q$, $\R$ and $\C$. Set theoretically speaking, they are related by inclusion, $\N$ is a proper subset of $\Z$ and so on.
We use natural numbers to count, we use integers to include both increase and decrease of a nutural number. When we want to divide
numbers, we have something which are not whole, we name all of them as rational numbers. However, rational numbers are not enough to measure any lengths in the real world, for example 
the length of the hypotenuse of a isosceles right triangle whose shorter sides are of length 1, we need real numbers. Complex number enable us to solve any equations.

In type theory, natural numbers are usually one of the primitive types. The other number systems are also quite common in proof assistants based on \itt{}, such as Agda, Coq and Epigram. Different from the situation in set theory, certain object in type theory can only have at most one type, which means the other number systems like integers, has to been defined separately and the set theoretical relation between two number systems has to be established explicitly. 

Based on different interpretations, we have multiple ways to define integers and rational numbers. The usual choices of implementation are normal forms. 
For example, the usual representation of integers are $\{ ... -3, -2, -1 , 0 ,1 ,2, 3 ... \}$. It can also been defined as a setoid, where the base type is
$\N\times\N$ and the equivalence relation is defined based on the interpretation that integers can be represented as 
the result of subtracting natural numbers from natural numbers.

In type theory, usually sets are of type "Set" rather than of type "Setoid". That means the quotient sets corresponding to the setoids should be more
preferable. In the case of integers, the normal forms just formalise the quotient set with respect to the setoid representation. Since the quotient set is definable,
it is unnecessary to use the setoid representation. However, the setoid representation is more elegant than the normal form one. The advantage of it is that there is only one form while there are at least
two forms for the canonical ones, positive and negative integers. Functions with integer arguments can be defined with less cases and theorems for integers can
 be proved simpler.

So we were thinking whether there is any approach to mix these two together so that we have the merits of both. Fortunately we found that we could use a definable quotient structure \cite{aan} which
includes the conversion functions between setoids and sets and lifting functions. Categorically speaking, it is an exact coequalizer.

This will explain why definable quotients are useful with the example of numbers, where we can do high level reasoning instead of reasoning of normal forms.




%Motivation of this : why definable quotients are useful (use example of numbers)

%Main goal : In some cases we can define quotients, we can do high level reasoning instead of reasoning of normal forms.



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

And this is exactly the definition in Agda standard library version 0.6. For each integer there is one unique representation so extra equivalence relation is not needed. However intuitively we lose the "special position" held by 0. Of course we can define three cases definition with distinct 0 constructor but too many cases are not ideal for proving. Using this definition we can define addition as

\begin{code}

-- An auxilliary operation: subtraction of natural numbers

_⊖_ : ℕ → ℕ → ℤ
m       ⊖ ℕ.zero  = + m
ℕ.zero  ⊖ ℕ.suc n = -[1+ n ]
ℕ.suc m ⊖ ℕ.suc n = m ⊖ n

_+_ : ℤ → ℤ → ℤ
-[1+ m ] + -[1+ n ] = -[1+ suc (m ℕ+ n) ]
-[1+ m ] + +    n   = n ⊖ ℕ.suc m
+    m   + -[1+ n ] = m ⊖ ℕ.suc n
+    m   + +    n   = + (m ℕ+ n)

\end{code}



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
 Since this definition has only one case, we don't need to define or prove for multiple cases. For example, the common operations defined on $\Z_0$($\bigslant{\N\times\N}{\sim}$) has only one case which are simpler than the one for the previous definition,

\begin{code}

_+₀_ : ℤ₀ → ℤ₀ → ℤ₀
(x1 , x2) +₀ (y1 , y2) = (x1 ℕ+ y1) , (x2 ℕ+ y2)

\end{code}

The elegant definition leads to elegant proofs of the properties of integers. For example, we can easily prove the distributivity laws for it.


\begin{code}

-- distʳ : _*_ DistributesOverʳ _+_
-- distʳ (a , b) (c , d) (e , f) = ℕ.dist-lemʳ a b c d e f +=
--                               ⟨  ℕ.dist-lemʳ b a c d e f ⟩

\end{code}

The right distributivity of multiplication over addition can be proved simply by proving something about natural numbers. This is because the definition of setoid integer is to represent integers using natural numbers, the operations is defined from the operations for natural numbers and finally the equality is an equation about natural numbers. That means all these properties are derivable. In fact, we can prove everything even simpler by using the automatic ring solver for natural numbers. The right distributivity for the two-case integers which is the library is much more cumbersome, the proof contains about 11 cases and about 70 lines long.


Back to addition for setoid integers, the operation is only valid when it respects the equivalence relation,

\begin{code}

_respects_ : {A : Set} → Op₂ A → Rel A _ → Set
_⊛_ respects _≈_ = ∀ a b c d → a ≈ b → c ≈ d → (a ⊛ c) ≈ (b ⊛ d)

\end{code}
Given two pairs equal setoid integers $(x , x₁) ∼ (x₂ , x₃)$ and $(x₄ , x₅) ∼ (x₆ , x₇)$, the goal just turns into some simple expression of natural numbers

$$x ℕ+ x₄ ℕ+ (x₃ ℕ+ x₇) ≡ x₂ ℕ+ x₆ ℕ+ (x₁ ℕ+ x₅)$$

which can be automatically solved in Agda (the detail looks cumbersome).

Given any operation respects the equivalence relation, we can easily
acquire the corresponding $\Z$ version operation by using a operation lifting function.

First, we need a function to find the corresponding $z : \Z$ for any given $z_0 : \Z_0$.
We can prove it is the kernel for the equivalence relation.
%We can call it the equivalent class function, since it send it into its equivalent class.


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

Then the general operation lifting function is

\begin{code}

lift₂   : (_⊛_ : Op₂ ℤ₀)
        → Op₂ ℤ
lift₂ _⊛_ a b = [ ⌜ a ⌝ ⊛ ⌜ b ⌝ ]

\end{code}

Indeed, we don't need the respects properties to define operation lifting function in this case since we can prove all lifted operation respects the equivalence relation, the lifted operation should have the same properties, which means we can also lift the proofs of the theorems on setoid integers.



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

\section{Definable quotients}

Quotient types is one of important extensional concepts\cite{hot:phd}. Generally a quotient type is some new type which is obtained by redefining equality on some existing type. It is unavailable in \itt{}, usually we can using setoids instead. However not all types are represented using setoids which means we lose unification for them. We have to define everything twice one for sets and one for setoids. Altenkirch's setoid model solves the problem by representing all sets using setoids. It is possible because usual sets can be seen as setoids whose equality are propositional equality for given sets.





\bibliographystyle{plain}
\bibliography{my}
\end{document}