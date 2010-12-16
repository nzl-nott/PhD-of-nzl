\documentclass[a4paper,12pt]{article}
\def\textmu{}
%include agda.fmt

\usepackage[utf8x]{inputenc}
\usepackage{ucs}

%\DeclareUnicodeCharacter{"2237}{\ensuremath{::}}
\DeclareUnicodeCharacter{"03BB}{\ensuremath{\lambda}}
\DeclareUnicodeCharacter{"03A3}{\ensuremath{\Sigma}}

\usepackage{color}
\newcommand{\txa}[1]{\textcolor{red}{\textbf{Thorsten:~}#1}}

\author{Li Nuo}
\title{Two presentations of equality}

\begin{document}

\maketitle

\section{Background}

We can define equality in two ways: either as an inductively defined
relation or as a parameterized inductive predicate:

\begin{description}
\item[As a binary relation]

\begin{code}
data Id (A : Set) : A → A → Set where
  refl : (a : A) → Id A a a
\end{code}

This one was first
proposed by Per Martin-Löf as intentional equality\cite{nord}.
There is one instance for each element.
We can treat equality relation as | (a , b) ∈ Id A |. We can describe it in
another way: it is a partition of the set |A x A|. 

\txa{As proposed Martin-Löf}
\item[As a predicate]
\begin{code}
data Id' (A : Set)(a : A) : A → Set where
  refl : Id' A a a
\end{code}
It is used in the Agda standard library. It is only
possible for us to define this one with dependent types because the
type depends on a value. We can treat |Id A
a| it as a predicate of whether certain element of type |A| is the same as
|a|. It also represents the singleton set with only one element |refl|
for each |Id A a|.
This one was proposed by Christine Paulin-Mohring.
\txa{proposed by Christine Paulin-Mohring}
\end{description}

For each of them, we have a corresponding elimination rule, defined as

\begin{description}
\item[As a binary relation]
\begin{code}
J : (A : Set)(P : (a b : A) → Id A a b → Set)
    → (m : (a : A) → P a a (refl a))
    → (a b : A)(p : Id A a b) → P a b p
J A P m .b b (refl .b) = m b
\end{code}
The |P| and |m| are not bounded by any value. |P| is actually a ternary
relation.
\txa{Use doublebar for all the inlined Agda code!}

|m| can be seen as an introduction rule for |P|. For all |a|, |(a , a, refl a)| is
inhabited in |P|. And the result is a more general
property, For all |a| |b|, |(a , b, x : Id A a b)| is inhabited in |P|.


|J| actually maps \[ |∀ (a : A) → P a a (refl a)|
\Rightarrow |∀ (a b : A)(p : Id A a b) → P a b p| \].

\item[As a predicate]
\begin{code}
J' : (A : Set)(a : A) 
  → (P : (b : A) → Id' A a b → Set)
  → (m : P a refl)
  → (b : A)(p : Id' A a b) → P b p
J' A .b P m b refl = m
\end{code}
The |P| and |m| are now bounded by the same |a| as the the identity
predicate. |P| and |m| here can be viewed as |P [a]|
and |m [a]|. Therefore, the elimination rule is all about eliminate
the predicate |Id ' A a| rather than the binary equivalence relation
|Id' A|.
 
|J'| actually maps  \[|P a refl| \Rightarrow |(b : A)(p : Id' A a b) → P b p|\].
|m|! can be seen as the only object in |P| and the result is used to unify
elements equal to a (a constant) to get the unique object.
\end{description}

\section{The Problem}
Now the problem is: how to implement |J| using only |J'| (also we use the
equality |Id'|) and vice versa? We will still use corresponding equality for each
elimination rule, otherwise it cannot eliminate the identity.

\section{Solution}

From |J'| to |J| is quite simple.
\txa{Which is the first direction?}
When we eliminate the predicate identity, we only need to create the
special cases of P and m for J'.
\begin{code}
JId' : (A : Set)(P : (a b : A) → Id' A a b → Set)
    → ((a : A) → P a a refl)
    → (a b : A)(p : Id' A a b) → P a b p
JId' A P m a = J' A a (P a) (m a)
\end{code}

\txa{Check that |JId' A P m .b b (refl .b) = m b| holds definitionally.}

The other direction is more tricky.
We first define |subst| from |J|

\begin{code}

subst : (A : Set)(a b : A)(p : Id A a b)
        (B : A → Set) → B a → B b
subst A a b p B = J A (λ a' b' _ → B a' → B b') (λ _ → id) a b p
\end{code}

Then to prove |J'| from |J| and |Id|,
\begin{code}

Q : (A : Set)(a : A) → Set
Q A a = Σ A (λ b → Id A a b)

J'Id : (A : Set)(a : A) → (P : (b : A) → Id A a b → Set)
  → P a (refl a)
  → (b : A)(p : Id A a b) → P b p
J'Id A a P m b p = subst (Q A a) (a , refl a) (b , p)
  (J A (λ a' b' x → Id (Q A a') (a' , refl a') (b' , x))
  (λ a' → refl (a' , refl a')) a b p) (uncurry P) m
\end{code}
We can not just use |J| to eliminate the identity because |J| requires
more general |P| and |m|.
We need to formalise the result |P b p| from |P a (refl a)|. We cannot
substitute |a| or |refl a| separately because the second argument is
dependent on the first argument. So when we substitute we should reveal
the dependent relation. 
\txa{Or : Instead we are going to substitute them simultanously using a dependent product.}

We could use dependent productr to do this work. In this way, we can
substitute them simultaneously. The problem now becomes substitute in
\begin{code} P ((λ a : A p : Id A a b → (a , p)) a (refl a)) \end{code} to \begin{code} P ((λ a : A p : Id A a b → (a , p)) b p) \end{code}

From |J|, we have |Id (Q a) (a , refl a) (b , x : Id a b)| so that we can
prove |P' (b , p)| from |P' (a , refl a)| using subst. Because |P' ( b
, p)| is namely |P b p|, we have proved.

\txa{Check that |J'Id A b P m b refl = m| holds definitionally!}

\txa{Add some references. For Id refer to the Nordstroem et al book, Thomas Streicher habil, Palmgren}

\txa{Compare with the construction of the isomorphism.}

\end{document}