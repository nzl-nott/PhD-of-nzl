\documentclass{article}

\usepackage{agda}

\usepackage{dsfont}
\usepackage{amsthm}

\usepackage{color}
\usepackage{amsmath}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{autofe}


\newcommand{\todo}[1]{\textcolor{red}{TO~DO:~#1}}

\newcommand{\ed}[1]{\textcolor{blue}{#1}}

\newcommand{\N}{\mathbb{N}}
\newcommand{\Q}{\mathbb{Q}}
\newcommand{\R}{\mathbb{R}}
\newcommand{\Z}{\mathbb{Z}}

\newcommand{\bigslant}[2]{{\raisebox{.2em}{$#1$}\left/\raisebox{-.2em}{$#2$}\right.}}

\begin{document}

\AgdaHide{
\begin{code}
module Definability where 

open import Data.Nat
\end{code}
}

% Title
\title{Numbers, quotients, and definability of reals}

\author{Li Nuo}

%\date{June 07, 2012}

\maketitle

% TOC
%\tableofcontents

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
  -[1+_] : (n : ℕ) → ℤ  -- -[1+ n ] stands for - (1 + n).
  +_     : (n : ℕ) → ℤ  -- + n stands for n.

\end{code}

And this is exactly the definition in Agda standard library version 0.6. This definition is easy to use since it has two cases and for each integer you have one unique representation. However intuitively we lose the "special position" held by 0. Of course we can define three cases definition with distinct 0 constructor but too many cases are not ideal for proving.

Alternatively we have another isomorphism between $\Z$ and
$\bigslant{\N\times\N}{\sim}$, namely constructing the set of integers
from quotienting the set of $\N\times\N$ by the following equivalence relation :

\begin{equation}
(n_1 , n_2) \sim (n_3 , n_4)\iff n_1 + n_4 = n_3 + n_2
\end{equation}
 
This implementation better exploits the relationship between the set of
natural numbers and the set of integers, because any integer is a
result of subtracting two natural numbers which means we uniformly
represent all integers, and the laws for basic operations are simpler
to lifted from the ones for natural numbers.

This kind of relationship between setoids and sets can be generalized
as quotient. If we have a setoid, we can define a corresponding
quotient type as $ Q : Set $ and a function $  [ \cdot ]
: A → Q $ such that we have


\begin{enumerate}


\item{soundness properties} 

$$ sound : ∀ {a b : A} → a ∼ b → [ a ] ≡ [ b ]$$

\item{an eliminator of quotient types} 

$$qelim   : {B : Q → Set}$$
$$            → (f : (a : A) → B [ a ])$$
$$            → ((a b : A) → (p : a ∼ b) $$
$$           → subst B (sound p) (f a) ≡ f b)$$
$$            → (q : Q) → B q$$

\item{the computational rule for the eliminator} 

$$qelim-β : ∀ {B a f} q → qelim {B} f q [ a ]  ≡ f a$$

\end{enumerate}




%\bibliographystyle{plain}
%\bibliography{literature}
\end{document}