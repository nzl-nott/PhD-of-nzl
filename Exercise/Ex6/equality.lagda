\documentclass[a4paper,12pt]{article}
\def\textmu{}
%include agda.fmt

\usepackage[utf8x]{inputenc}
\usepackage{ucs}
\usepackage{cite}

%\DeclareUnicodeCharacter{"2237}{\ensuremath{::}}
\DeclareUnicodeCharacter{"03BB}{\ensuremath{\lambda}}
\DeclareUnicodeCharacter{"03A3}{\ensuremath{\Sigma}}

\usepackage{color}
\newcommand{\txa}[1]{\textcolor{red}{\textbf{Thorsten:~}#1}}

\newcommand{\nzl}[1]{\textcolor{green}{\textbf{Nuo:~}#1}}

\author{Li Nuo}
\title{Two presentations of equality in dependently typed languages}

\begin{document}

\maketitle

\section{Background}

In intensional type theory, propositional equality (establish equality based on identity) can be defined in two ways: either defined as an inductive
relation or as a parameterized inductive predicate:

\begin{description}
\item[As a binary relation] \hspace*{\fill} \\

\begin{code}
data Id (A : Set) : A → A → Set where
  refl : (a : A) → Id A a a
\end{code}

This one was first
proposed by Per Martin-Löf as propositional equality\cite{Nord}. |refl| here is a function which creates a single equality term for each element of A.


\item[As a predicate] \hspace*{\fill} \\


\begin{code}
data Id' (A : Set)(a : A) : A → Set where
  refl : Id' A a a
\end{code}
This version was proposed by Christine Paulin-Mohring \cite{coq} and is adopted in the Agda standard library. The formalisation of this identity type requires the equated value.
|Id' A a| can be seen as a predicate of whether some | x : A | is the same as
|a| in the type declaration. Since the equated value has been determined within the type, we only need an unique proof |refl|.

\end{description}

In intensional type theory, we have a corresponding elimination rule for each of them. It was
called |idpeel| in \cite{Nord} but we use the common name |J| here. We can easily define it using pattern matching in Agda as below.

\begin{description}
\item[As a binary relation] \hspace*{\fill} \\


\begin{code}
J : (A : Set)(P : (a b : A) → Id A a b → Set)
    → (m : (a : A) → P a a (refl a))
    → (a b : A)(p : Id A a b) → P a b p
J A P m a .a (refl .a) = m a
\end{code}
|P| is the proposition dependent on the equality. |m| is function to create inhabitant for this proposition when we we know the two sides of the identity term are definitionally equal. Using pattern matching we can easily derive that the equality term must only be constructed by the function |refl| and if it is inhabitant, the two sides must be identical. Then |P a b p| can be turned into |P a a (refl a)| so that we can trivially formalise it using |m a|. 

The main ingredient of |J| is pattern matching |(a , b , p : Id A a b)| with |(b , b , refl b)|.

\item[As a predicate] \hspace*{\fill} \\


\begin{code}
J' : (A : Set)(a : A) 
  → (P : (b : A) → Id' A a b → Set)
  → (m : P a refl)
  → (b : A)(p : Id' A a b) → P b p
J' A .a P m a refl = m
\end{code}
For |Id' A a|, since the type formalisation requires one side of the equality, we treat it as a predicate on the other side of the equality. Therefore, within the elimination rule, |Id' A a| is fixed, which means |P|, |m| and |p| now share the same free variable |a| as in |Id' A a|. Then |m| becomes the proof that P is only valid when the other side is the same as |a|. Also with pattern matching, |(b , p : Id' A a b)| is identified with |(a , refl : Id' A a a)|. Hence, |P b p| can be turned into |P a refl| which is just |m|. 

\end{description}

These two formalisation of equality can be used alternatively in many places. They should be ispomorphic in intensional type theory. We can easily prove it as below. 


\txa{Compare with the construction of the isomorphism.}
\nzl{I need to rewrite it in Agda}

What is more interesting is the question below.

\section{The Question}
Now the question is: how to implement |J| using only |J'| and vice versa? We will still use corresponding equality to be used by each
elimination rule.

\section{The Solution}

From |J'| to |J| is quite simple. If we assume a is the left hand side, and we rename |P a| with |P'|, then |J' A a P' (m a)| can turn |P' b p| for some |b| into |P' a refl| which is just |m a|.

\begin{code}
JId' : (A : Set)(P : (a b : A) → Id' A a b → Set)
    → ((a : A) → P a a refl)
    → (a b : A)(p : Id' A a b) → P a b p
JId' A P m a = J' A a (P a) (m a)
\end{code}

We can easily verfiy it by definitionally expanding J'.

The other direction is more tricky, because for |J'| we have proposition |P|, proof term |m| and equality term |p| dependent on the same value |a| which is not trivially suited for |J|. We must try to devise other ways to solve it.

We first define |subst| from |J|

\begin{code}

subst : (A : Set)(a b : A)(p : Id A a b)
        (B : A → Set) → B a → B b
subst A a b p B = J A (λ a' b' _ → B a' → B b') (λ _ x → x) a b p

Q : (A : Set)(a : A) → Set
Q A a = Σ A (λ b → Id A a b)

J'Id : (A : Set)(a : A) → (P : (b : A) → Id A a b → Set)
  → P a (refl a)
  → (b : A)(p : Id A a b) → P b p
J'Id A a P m b p = subst (Q A a) (a , refl a) (b , p)
  (J A (λ a' b' p' → Id (Q A a') (a' , refl a') (b' , p'))
  (λ a' → refl (a' , refl a')) a b p) (uncurry P) m
\end{code}
The idea behind it is that we need to identify |P b p| with |P a refl|. We cannot
substitute |b| with |a| or |p| with |refl a| independently because the second argument is
dependent on the first argument. we must substitute them simultaneously. Therefore it is natural to use a dependent product.
It happens simultaneously when we use pattern match to prove it.

We use a function |Q| to form the dependent product. To substitute |(b , p)| with |(a , refl a)| we must have the equality term |Id (Q a) (a , refl a) (b , p)|.
We can easily get this term using |J|. So we have done the proof. Also we can expand it definitionally to verfy it.

The question shows that no matter which formulation of equality and which elimination rule we have, we can prove the other elimination rule for the other formulation of equality.

\txa{Add some references. For Id refer to the Nordstroem et al book, Thomas Streicher habil, Palmgren}


\bibliography{equality1}{}
\bibliographystyle{plain}

\end{document}