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

The right distributivity of multiplication over addition can be proved simply by proving something about natural numbers. This is because the definition of setoid integer is to represent integers using natural numbers, the operations is defined from the operations for natural numbers and finally the equality is an equation about natural numbers. That means all these properties are derivable. In fact, we can prove everything even simpler by using the automatic ring solver for natural numbers. The right distributivity for the two-case integers which is the library is much more cumbersome

\begin{verbatim}



distribʳ : _*_ DistributesOverʳ _+_

distribʳ (+ zero) y z
  rewrite proj₂ *-zero ∣ y ∣
        | proj₂ *-zero ∣ z ∣
        | proj₂ *-zero ∣ y + z ∣
        = refl

distribʳ x (+ zero) z
  rewrite proj₁ +-identity z
        | proj₁ +-identity (sign z S* sign x ◃ ∣ z ∣ ℕ* ∣ x ∣)
        = refl

distribʳ x y (+ zero)
  rewrite proj₂ +-identity y
        | proj₂ +-identity (sign y S* sign x ◃ ∣ y ∣ ℕ* ∣ x ∣)
        = refl

distribʳ -[1+ a ] -[1+ b ] -[1+ c ] = cong +_ $
  solve 3 (λ a b c → (con 2 :+ b :+ c) :* (con 1 :+ a)
                  := (con 1 :+ b) :* (con 1 :+ a) :+
                     (con 1 :+ c) :* (con 1 :+ a))
          refl a b c

distribʳ (+ suc a) (+ suc b) (+ suc c) = cong +_ $
  solve 3 (λ a b c → (con 1 :+ b :+ (con 1 :+ c)) :* (con 1 :+ a)
                  := (con 1 :+ b) :* (con 1 :+ a) :+
                     (con 1 :+ c) :* (con 1 :+ a))
        refl a b c

distribʳ -[1+ a ] (+ suc b) (+ suc c) = cong -[1+_] $
  solve 3 (λ a b c → a :+ (b :+ (con 1 :+ c)) :* (con 1 :+ a)
                   := (con 1 :+ b) :* (con 1 :+ a) :+
                      (a :+ c :* (con 1 :+ a)))
         refl a b c

distribʳ (+ suc a) -[1+ b ] -[1+ c ] = cong -[1+_] $
  solve 3 (λ a b c → a :+ (con 1 :+ a :+ (b :+ c) :* (con 1 :+ a))
                  := (con 1 :+ b) :* (con 1 :+ a) :+
                     (a :+ c :* (con 1 :+ a)))
         refl a b c

distribʳ -[1+ a ] -[1+ b ] (+ suc c) = distrib-lemma a b c

distribʳ -[1+ a ] (+ suc b) -[1+ c ] = distrib-lemma a c b

distribʳ (+ suc a) -[1+ b ] (+ suc c)
  rewrite +-⊖-left-cancel a (c ℕ* suc a) (b ℕ* suc a)
  with b ≤? c
... | yes b≤c
  rewrite ⊖-≥ b≤c
        | +-comm (- (+ (a ℕ+ b ℕ* suc a))) (+ (a ℕ+ c ℕ* suc a))
        | ⊖-≥ (b≤c *-mono ≤-refl {x = suc a})
        | ℕ.*-distrib-∸ʳ (suc a) c b
        | +‿◃ (c ℕ* suc a ∸ b ℕ* suc a)
        = refl
... | no b≰c
  rewrite sign-⊖-≱ b≰c
        | ∣⊖∣-≱ b≰c
        | -‿◃ ((b ∸ c) ℕ* suc a)
        | ⊖-≱ (b≰c ∘ ℕ.cancel-*-right-≤ b c a)
        | ℕ.*-distrib-∸ʳ (suc a) b c
        = refl

distribʳ (+ suc c) (+ suc a) -[1+ b ]
  rewrite +-⊖-left-cancel c (a ℕ* suc c) (b ℕ* suc c)
  with b ≤? a
... | yes b≤a
  rewrite ⊖-≥ b≤a
        | ⊖-≥ (b≤a *-mono ≤-refl {x = suc c})
        | +‿◃ ((a ∸ b) ℕ* suc c)
        | ℕ.*-distrib-∸ʳ (suc c) a b
        = refl
... | no b≰a
  rewrite sign-⊖-≱ b≰a
        | ∣⊖∣-≱ b≰a
        | ⊖-≱ (b≰a ∘ ℕ.cancel-*-right-≤ b a c)
        | -‿◃ ((b ∸ a) ℕ* suc c)
        | ℕ.*-distrib-∸ʳ (suc c) b a
        = refl

\end{verbatim}





Back to addition for setoid integers, the operation is only valid when it respects the equivalence relation,

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

The quotient types enables redefining equality on types and it is also an extensional concept\cite{hot:phd}. It is unavailable in \itt{}, usually we can using setoids instead. However not all types are represented using setoids which means we lose unification for them. We have to define everything twice one for sets and one for setoids. Altenkirch's setoid model solves the problem by representing all sets using setoids. It is possible because usual sets can be seen as setoids whose equality are propositional equality for given sets.



\section{definability}







\bibliographystyle{plain}
\bibliography{my}
\end{document}