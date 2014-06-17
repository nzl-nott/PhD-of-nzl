\section{How to define numbers in Agda?}
We have understood what are numbers in mathematics. Then we will discuss how to represent them in Agda. There are several choices of definitions, some are more intuitive to people and some are more meaningful mathematically.

\begin{itemize}
\item $\mathds{N}$ - \textit{Natural numbers.} In the base ten system, we can represent natural numbers by using digits from 0 to 9. However it is hard to write this definition in Agda as there are infinite digits. The inductive definition solves the problem efficiently.
In Peano Arithmetic, the following inductive definition is widely used to define natural numbers and operations in programing languages like Haskell, Coq and Agda,
\begin{definition}
\begin{code}
data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ
\end{code}
\end{definition}
This can be seen as a natural definition because it simulates the process of incrementing numbers.

\item $\mathds{Z}$ - \textit{Integers.} As we mentioned before, integers add negative numbers to natural numbers. To represent it normally, we only need to add a sign in front of natural numbers to differentiate positive and negative numbers,
\begin{definition}
\begin{code}
data ℤ : Set where
  +_    : (n : ℕ) → ℤ
  zero  : ℤ
  -_    : (n : ℕ) → ℤ
\end{code}
\end{definition}
But in this definition the definition is ambiguous. If "$+ 0$", "$- 0$" and "zero" all represent 0 then, the uniqueness of zero is lost and the basic definitional equality does not work for it. The definitional equality holds for two definitionally same elements. We can simply prove this equality by using "refl". If we need "$+ 0$" to represent "$+ 1$", it is better to define it like follows,

\begin{definition}
\begin{code}
data ℤ : Set where
  +suc_    : (n : ℕ) → ℤ
  zero     : ℤ
  -suc_    : (n : ℕ) → ℤ
\end{code}
\end{definition}

Although definition looks symmetric and non-misleading, it has three patterns which increase the number of cases to pattern match when doing definition and theorem proving. For instance, when we prove the associativity for +,

\begin{theorem}[Associativity]
$\forall x y z, (x + y) + z = x + (y + z)$
\end{theorem}

In the worst case, we have to pattern match on each of the three numbers so that there will be 27 cases at most. To reduce cases, we could combine zero and positive integers,

\begin{definition}
\begin{code}
data ℤ : Set where
  +_    : (n : ℕ) → ℤ
  -suc_ : (n : ℕ) → ℤ
\end{code}
\end{definition}
This definition is my choice for normal integer in this project as there is less cases. The asymmetry does not make too much trouble.


All the definition above are intuitive definitions and I call the last one normal definition in this project. 
Alternatively, we could also use a pair of natural numbers to represent an intger as we discussed before,
\begin{definition}
\begin{code}
ℤ₀ = ℕ × ℕ
\end{code}
\end{definition}
it represents the result of subtraction between the two numbers, and the single pattern shorten the proof. However it is an incomplete definition unless we combine a propositional equality with it. Propositional equality is a relation defined specially according to mathematics. Here, we could easily found that $(3, 2)$ and $(2, 1)$ both represent $+ 1$ but will not be treated equal by definition because they are not the same. To be isomorphic to the set of the integers we have to define the equivalence relation of it so that they could form a setoid.

\begin{definition}
\begin{code}
_∼_ : Rel ℤ₀ zero
(x+ , x-) ∼ (y+ , y-) = (x+ ℕ+ y-) ≡ (y+ ℕ+ x-)
\end{code}
\end{definition}

We should firstly prove the relation is equvalence.

a) reflexivity: ∀ a → a ∼ a

\begin{code}

refl : Reflexive _∼_

\end{code}

b) symmetry: ∀ a b → a ∼ b → b ∼ a

\begin{code}

sym : Symmetric _∼_

\end{code}

c) transitivity:  ∀ a b c → a ∼ b /\ b ∼ c → a ∼ c

\begin{code}

trans : Transitive _∼_

\end{code}

Now with these three properties we could prove it is equivalence relation,

\begin{code}

_∼_isEquivalence : IsEquivalence _∼_
_∼_isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

\end{code}

Then we can prove that (ℤ₀, ∼) is a setoid

\begin{code}
isSetoid : Setoid _ _
isSetoid = record
  { Carrier       = ℤ₀
  ; _≈_           = _∼_
  ; isEquivalence = _∼_isEquivalence
  }
\end{code}

I call this kind of integers as setoid integers in this project. The drawback of this representation is that it looks not intuitive to people so it is not a good choice for user. But the benefit for proving is precious so I explore the ways to define both normal definition and setoid one in this project and combine the advantage of both. The mechanism between the two definitions is to firstly define and prove properties for setoid integers and then define the operations of the normal definition on the setoid on using normalisation functions and denormalisation functions,

\textbf{Normalisation}

normalise the setoid integer to normal form

\begin{code}

[_]               : ℤ₀ → ℤ
[ m , 0 ]         = + m
[ 0 , suc n ]     = -suc n
[ suc m , suc n ] = [ m , n ]

\end{code}

denormalise the normal integer to one representative setoid integer

\begin{code}

⌜_⌝        : ℤ → ℤ₀
⌜ + n ⌝    = n , 0
⌜ -suc n ⌝ = 0 , suc n

\end{code}

Then we could prove the isomorphism of the setoid and the normal definition,

a) stability:
nf is left inverse of dn

\begin{theorem}
\begin{code}

stable            : ∀ {n} → [ ⌜ n ⌝ ] ≡ n

\end{code}
\end{theorem}

b) completeness:
if it is true, then we can give the proof

\begin{theorem}
\begin{code}

compl                   : ∀ {n} → ⌜ [ n ] ⌝ ∼ n

\end{code}
\end{theorem}

c) soundness:
if we proved it, then it is true

\begin{theorem}
\begin{code}

sound                 : ∀ {x y} → x ∼ y → [ x ] ≡ [ y ]

\end{code}
\end{theorem}

Using the setoid and the three theorems above, we could form the quotient type of integer.

\begin{code}

ℤ-QuSig : QuSig isSetoid
ℤ-QuSig = record
  { Q       = ℤ
  ; [_]     = [_]
  ; sound   = sound
  }

ℤ-Nf : Nf ℤ-QuSig
ℤ-Nf = record
  { emb       = ⌜_⌝
  ; compl     = λ z → compl
  ; stable    = λ z → stable
  }

\end{code}
The general quotient type theory was developed by Thomas Anberrée and Thorsten Altenkirch. It is a mechanism designed to simplify the theorem proof of the normal form by lifting the theorems of setoid form. However there is still some problems in applying the lift functions.

\item $\mathds{Q}$ - \textit{Rational numbers.} Rational numbers as quotients of integers will be naturally defined as a pair of integers. The decimal representation which is more common is practice requires infinite digits which is inefficient and imprecise in computer science which use discrete mathematics in general.

To construct the rational numbers in the fractional form, there are several choices:

\begin{enumerate}
\item a pair of ℤ
\begin{definition}
\begin{code}
data ℚ₀ : Set where
  _/_ : (n : ℤ) → (d : ℤ) → ℚ₀
\end{code}
\end{definition}

The benifit is the types of numerator and denominator are consistent. But the non-zero restriction of the denominator is hard to reflect in this definition.

\item a pair of ℕ with symbol
\begin{definition}
\begin{code}
data ℚ₀* : Set where
  _/suc_ : (n : ℕ) → (d : ℕ) → ℚ₀*
  
data ℚ₀ : Set where
  +_ : ℚ₀* → ℚ₀
  -_ : ℚ₀* → ℚ₀
\end{code}
\end{definition}

Compared to integers, to deal with lower natural numbers is simpler. However there are two cases which makes the definition of operatio ns and the proof much longer. Moreover, it makes little difference with the following definition,

\item ℤ × ℕ
\begin{definition}
\begin{code}
data ℚ₀ : Set where
  _/suc_ : (n : ℤ) → (d : ℕ) → ℚ₀
\end{code}
\end{definition}
Because O is easier to excluded for ℕ, we choose to combine the sign with the numerator. We only need to show that we use n to denote successor of n in the denominator. This is what I choose in my project. Also, it is a setoid definition so that we should define equivalence relation for it,
\end{enumerate}

\begin{definition}
\begin{code}
_∼_   : Rel ℚ₀
n1 /suc d1 ∼ n2 /suc d2 =  n1 ℤ*ℕ suc d2 ≡ n2 ℤ*ℕ suc d1
\end{code}
\end{definition}

There is also normal definition of rational numbers. When we simplify the numerator and denominator to become coprime, then we can infer they are the same from equality. As the representative of for each rational numberis unique, we get definitional equality,

\begin{definition}
\begin{code}
record ℚ : Set where
  constructor _/suc_,[_]
  field
    numerator   : ℤ
    denominator : ℕ
    isCoprime   : Coprime (ℤtoℕ n) (suc d)
\end{code}
\end{definition}

This normal definition has been available in the 0.3 version standard library. However there is limited amount of functions defined.

\item $\mathds{R}$ - \textit{Real numbers.} To define real numbers is much more complicated work. In computer science we mostly deals with discrete mathematics, but real numbers is continuous. Therefore in most commercial used programming languages, programmer use types like double, float which have finite decimals to represent a real number for practical use as they are more efficient. However it is not precise to omit the the infinit tail of an irration number. If we want to prove properties for real numbers, we need to define ‘real’ real numbers.

There are various ways to construct real numbers : Cauchy sequences of rational numbers, Dedekind cuts, decimal expansion and etc. \cite{wiki:Real}
In this project we follow the development of Bishop \cite{bishop} to construct real numbers. It uses a Cauchy sequence, namely an infinite sequence of rational numbers whose elements become Arbitrarily close and converge to certain real number. 

For example: To represent $\sqrt{2}$ we could use the sequence,

\begin{center}
$1, 1.4, 1.41, 1.414, 1.4142, 1.41421. . .$
\end{center}

To generate the sequence we could use general function and a proof of the elements in the sequence generated from the general function complete Cauchy sequence, namely the sequence converges,

\begin{definition}
\begin{code}
record ℝ₀ : Set where
  constructor _,[_]
  field
    f : ℕ → ℚ
    p : ∀ ε → (ε > 0) → ∃ λ N →
    	(m n : ℕ) → (m > N) → (n > N) → ∣ (f m) - (f n) ∣< ε
\end{code}
\end{definition}

or use a stream of rational numbers which is a coninductive type in Agda,

\begin{definition}
\begin{code}
record ℝ₀ : Set where
  constructor _,[_]
  field
    s : Stream ℚ
    p : ∀ ε → (ε > 0) → ∃ λ N →
    	(m n : ℕ) → (m > N) → (n > N) →
    	∣ (lookup m s) - (lookup n s) ∣< ε
\end{code}
\end{definition}

There are infinite number of Cauchy sequences representing the same real numbers, so this is also a setoid definition. Two Cauchy sequences (X and Y) are called equivalent if and only if for every positive rational number $\epsilon$, there exists an integer N such that $\vert X{n} - Y{n} \vert < \epsilon$ for all $n > N$. Hence the equivalence relation could be defined as,

\begin{definition}
\begin{code}
_∼_   : Rel ℝ₀
X ,[ _ ] ∼ Y ,[ _ ] = 
	∀ ε → is+ ε → ∃ λ N →
	(n : ℕ) → (n > N) →  ∣ (X n) - (Y n) ∣ < ε
\end{code}
\end{definition}

As we could not gives each of the infinite elements manually, Then the Taylor Series \cite{wiki:TS} should be used to generate a general functions of the sequence for different real numbers. It is better to define the real numbers as a general function rather than an infinite stream which may not contain the information of the general function. Therefore I use the first one in this project.

Actually, unlike integers and rational numbers, real numbers have no normal forms. Georg Cantor has famously proved that the set of reals is uncountable infinite in his first uncountability proof\cite{cantor}. It means that the cardinality of reals, $\mathfrak{c}$, is strictly greater than the cardinality of the set of natural numbers, $\aleph_{0}$, which equals to the one of integers and the one of rational numbers,
$\aleph_{0} < \mathfrak{c}$

Another famous construction method is Dedekind cuts. It can be defined as a partition of an ordered field (A, B), such that A is closed downwards, B is closed upwards and both of them are non-empty. In fact as A determines B we can use only A to represent a real number.

Intuitively, a real number is represented by all rational numbers which are less than it. It looks simpler than Cauchy sequence, but it is difficult to formlise a way to generate the dedekind cut in Agda. For example, if we want to represent $\sqrt{2}$,

\begin{center}
$A = \lbrace x \in \mathds{Q} : x < 0 \bigvee x \times x < 2 \rbrace $
\end{center}
There is no general way to construct a dedekind cut.


\item $\mathds{C}$ - \textit{Complex numbers.} After defining real numbers, the complex numbers will be easy to define. It consists of a real part and an imaginary part whose coefficient is also a real number. Similarly we could represent it as a pair of real numbers but it is not a setoid definition as it is unique representation.

\begin{definition}
\begin{code}
ℂ = ℝ × ℝ
\end{code}
\end{definition}

\end{itemize}