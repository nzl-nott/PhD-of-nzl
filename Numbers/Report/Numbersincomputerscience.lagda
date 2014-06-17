\section{What are differences of numbers in computer science?}
\begin{enumerate}
\item In regular mathematics, each lower level numbers is a subset of the higher level ones. For example 3 is a natural number, but it is also a integer, a rational number, a real number and a complex number. In fact these kinds of types are a categorized subset of all of the numbers which have the same features.

However in computer science, or we should say in most of the programming languages, different kinds of numbers are defined as different types. It means that 3 of type natural numbers is recognised as a different value to + 3 of type integers, although they refer to the same number in mathematics. Therefore we should define operators and prove properties for each kind of numbers. If you wonder why not just define all of the number as a single type, I think the answer is that there is dependence between lower level numbers and higher level ones, for example, it is more convenient to define integers based on natural numbers as it is an extention of natural numbers.
Especially for real numbers, to precisely construct real numbers we have to use natural numbers and rational numbers and we will talk about it later.

\item In regular mathematics, we postulate not only the existence of numbers but also some basic theorems as axioms like commutativity, associativity and distributivity. We can freely use them in computation for all kinds of numbers. We believe they are true from when we were young but we do not need to prove them to be true.

However in programming languages, although these theorems looks trivial, as we construct the numbers from scratch, we do not have any proofs of these axioms. These axioms are actually provable. To enable users to prove more advanced properties, we have to figure out the proof of them based on the only postulate ’refl’ which means we only need to admit it is true that if two things are the same then they are equal.

\item In regular mathematics, we could express numbers in different forms. For example, $\frac{1}{2}$ is the same as $0.5$ and both representations of rational numbers can be used simultaneously.
However, in Agda, if we choose to represent rational numbers in fractional form, we could not mix it with the decimal representation except when we use polymorphism.

Generally, the rules for numbers are more rigorous in computer science. What is postulate in Agda is limited.
For equality we only postulate when two numbers are the same they are equal,

\begin{definition}
\begin{code}
data _≡_ {a} {A : Set a} (x : A) : A → Set where
  refl : x ≡ x
\end{code}
\end{definition}

For unequality,

\begin{definition}
\begin{code}
data _≤_ : Rel ℕ zero where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n
\end{code}
\end{definition}

all the other axioms inregular mathematics requires to be defined or to be proved.
\end{enumerate}