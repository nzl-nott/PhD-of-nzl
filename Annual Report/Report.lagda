\AgdaHide{
\begin{code}

module Report where

open import Data.Nat
open import Relation.Binary
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Data.Nat.GCD
open import Data.Nat.Divisibility using (_∣_ ; 1∣_ ; divides)
import Data.Nat.Coprimality as C
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

ℤ₀ = ℕ × ℕ

\end{code}
}

\documentclass{article}
\def\textmu{}
\author{Li Nuo}
\title{First Year PhD Annual Report}

%\setlength{\textheight}{20cm}
%\setlength{\textwidth}{5.5in}
%\setlength{\topmargin}{-0.1in}
%\setlength{\oddsidemargin}{-1.8mm}
%\setlength{\evensidemargin}{-1.8mm}

%\institute{University of Nottingham}

\usepackage{dsfont}
\usepackage{amsthm}

%include agda.fmt

\usepackage{color}
\usepackage{amsmath}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{autofe}
\usepackage{url}


\theoremstyle{definition}
\newtheorem{definition}{Definition}[section]

\DeclareUnicodeCharacter{955}{$\lambda$}
\DeclareUnicodeCharacter{8988}{$\ulcorner$}
\DeclareUnicodeCharacter{8990}{$\llcorner$}
\DeclareUnicodeCharacter{8989}{$\urcorner$}
\DeclareUnicodeCharacter{8991}{$\lrcorner$}
\DeclareUnicodeCharacter{946}{$\beta$}

\newcommand{\todo}[1]{\textcolor{red}{TO~DO:~#1}}

\newcommand{\ed}[1]{\textcolor{blue}{#1}}

\newcommand{\N}{\mathbb{N}}
\newcommand{\Q}{\mathbb{Q}}
\newcommand{\R}{\mathbb{R}}
\newcommand{\Z}{\mathbb{Z}}


\newcommand{\dotph}{\,\cdot\,}
\newcommand{\dotop}{\mathrel{.}}
\providecommand{\abs}  [1]{\lvert#1\rvert}
\providecommand{\norm} [1]{\lVert#1\rVert}
\providecommand{\class}[1]{[#1]}
\providecommand{\set}  [1]{\left\{#1\right\}}
\providecommand{\dlift}[1]{\widehat{#1}}

\DeclareMathOperator{\Prop}{\mathbf{Prop}}
\DeclareMathOperator{\Set}{\mathbf{Set}}
\DeclareMathOperator{\Ext}{Ext}
\DeclareMathOperator{\Bool}{Bool}
\DeclareMathOperator{\id}{id}
\DeclareMathOperator{\sound}{sound}
\DeclareMathOperator{\qelimbeta}{qelim-\beta}
\DeclareMathOperator{\qind}{qind}
\DeclareMathOperator{\exact}{exact}
\DeclareMathOperator{\subst}{subst}
\DeclareMathOperator{\emb}{emb}
\DeclareMathOperator{\complete}{complete}
\DeclareMathOperator{\stable}{stable}
\DeclareMathOperator{\List}{List}
\DeclareMathOperator{\Fin}{Fin}
\DeclareMathOperator{\now}{now}
\DeclareMathOperator{\later}{later}
\DeclareMathOperator{\nowequal}{now_\sqsubseteq}
\DeclareMathOperator{\laterequal}{later_\sqsubseteq}
\DeclareMathOperator{\laterleft}{later_{left}}
\DeclareMathOperator{\inl}{inl}
\DeclareMathOperator{\inr}{inr}
\DeclareMathOperator{\qelim}{qelim}
\DeclareMathOperator{\lift}{lift}
\DeclareMathOperator{\LC}{LC}
\DeclareMathOperator{\liftbeta}{lift-\beta}
\DeclareMathOperator{\Bijection}{Bijection}
\DeclareMathOperator{\true}{true}
\DeclareMathOperator{\false}{false}
\DeclareMathOperator{\sort}{sort}
\DeclareMathOperator{\length}{length}
\DeclareMathOperator{\nub}{nub}
\DeclareMathOperator{\suc}{suc\,}
\DeclareMathOperator{\defi}{\stackrel{\text{\tiny def}}{=}}
\DeclareMathOperator{\coprime}{Coprime}

\DeclareMathOperator{\A/sim}{A\,\, /\sim}

\newcommand{\eqqm}{\overset{\text{\tiny ?}}{=}}
\newcommand{\sep}{\mathrel{\sharp}}

% Shorthand
\newcommand{\itt}{Intensional Type Theory}
\newcommand{\ett}{Extensional Type Theory}
\newcommand{\mltt}{Martin-L\"{o}f type theory}

\newenvironment{codes}{\tiny\begin{code}}{\end{code}}

\usepackage{varioref}

\begin{document}

\maketitle

\tableofcontents

\newpage

\begin{abstract}
%\todo{enhance the connection within between ideas. Split the two
%ideas in the abstract: why in general quotient is useful and
%implementing in Agda.}


% use of quotients is a 
% types before objects rather than objects before in set theory
%  what is itt what is ett what is the diff and what implementation is
%  itt or ett? more detail and technical?
% always be more precise , give explanation, examples, list things,
% not use complicated
% what i want to do, plan, proposal, explain the context of that paper
% why it is good to use the quotient, examples. 
%suggestion: 
% 1. extend the txa:1999 to quotients, integrate quotients into these
% 2. to prove the conservativity of itt + quotients ove ett,
% formalisation and detail.
% 3. smaller goals on the way
% 4. what I have done formalise proofs in Agda. Develop the
% background. how I have done related to others, motivation, why it is
% interesting what I have read, diff between ett and itt. in my
% undergraduate thesis.
% 5. Plan and steps to achieve these.

In set theory, given a set equipped with an equivalence relation, one can form its
quotient set, that is the set of equivalence classes.
Reinterpreting this notion in type theory,quotient sets are called quotient types.
However quotient types are still
unavailable in \itt{} which is a very important type theory.
Quotients are very common in mathematics and computer science, and
thus the introduction of quotients could be very helpful.
Some types are less effective to define from scratch than being defined
as the quotients of some other types and their equivalence relations, such as the
set of integers.
Even some sets are impossible to define without being based on quotients such as the set of real
numbers.
Sometimes, quotient types are more difficult to reason about than
their base types. 
We can achieve more convenience by manipulating base types and then lifting the operators and propositions according to the relation between quotient types and base types.
Therefore it is worthwhile for us to conduct a research project on the
implementation of quotients in \itt{}.

The work of this project will be divided into several phases. This
report introduces the basic notions in my project on implementing
quotients in type theory, such as type theory setoids, and quotient
types, reviews some work related to this topic and concludes with some
results of the first phase. 
The results done by Altenkirch, Anberr\'{e}e and I in \cite{aan} will be explained with a
few instances of quotients.

\end{abstract}


\section{Introduction}

%Some general background?

% the notion of quotient
In mathematics, the result of division is called quotient.
Similar to product, the notion of a quotient is also extended to other more abstract branches of mathematics.
For example, we have quotient sets, quotient groups, quotient spaces and quotient categories.
They are all defined in this way: some collection of objects is partitioned by some equivalence relation and the set of the equivalent classes
is the quotient set which usually bears some algebraic structure inherited from
the structure of the original collection of objects.

% quotients in real life
Quotients are also common in our daily life. When you take a
picture with a digital camera, the real scene is divided into pixels
on the pictures, and a red point and a blue point on the real scene are indistinguishable on
the photo if they are represented by the same pixel. The digital picture which is the set of pixels is just the
quotient of the real scene. Since different things are equated
with respect to certain rules, a quotient is usually related to
information hiding or information losing.

% quotients in CS
Quotients also exist in computer science. Users are usually concerned with the extensional use of
softwares rather than the intensional implementation of them,
different implementations of softwares doing the same tasks are
treated as the same to them even though 
some of them are programmed in different languages. Another example is
the application of an \emph{interface} in Java. The objects of different classes implementing the same
interface |A| should be treated equally when we create new objects of type |A|, even
though they are not really the same.

However in some type theories, the construction of quotients remains
problematic. In this project, we are going to explore this topic in the intensional variant of \mltt{}
(See Section~\ref{tt}) which serves as the basis of some useful
functional programming languages or theorem provers such as Coq and
Agda. This report aims at introducing some basic notions used in this
project, reviewing related works and explaining some results that have
been done. 

The structure of this report is as follows:

Section~\ref{sec:bg} introduces some basic concepts such as type
theory and quotient types along with the discussion of the problems
that arise when implementing quotient types. To make them easier to understand, it
will start with quotients in set theory which may be
more familiar to many people. 

Section~\ref{sec:lr} reviews some related works. Some of them discuss
implementing quotient types in other type theories, some of them
introduce similar notions. There are also some works done in this area
but still require further extensions. These constitute the basis of this project.

Section~\ref{sec:ob} gives more detailed objectives and a plan of how
to achieve them.

Section~\ref{sec:rd} explains some results that have been done by the
author or by Altenkirch, Anberr\'{e}e and the author in \cite{aan}.

Section~\ref{sec:cl} concludes this report along with the discussion
of future works.

In Appendix, I will list the full versions of some codes within the
text which are less relevant. All the codes are written in Agda which
will be introduced later. The readers who are familiar with Agda
or interested in the codes could look up them there. To make the codes
more readable, I eliminate some unnecessary parts such as the universe polymorphism.

\section{Background}
\label{sec:bg}

In this report, I will mainly discuss quotients in type theory
which are usually referred to as quotient types. Although set theory and
type theory have different foundations, they have many similar
notions such as product and disjoint union.  In this case, a quotient type
is also an interpretation of a quotient set in set theory.

\subsection{Quotient Sets} 

The division of sets is different from division of numbers. We divide a
given set into disjoint subsets according to a given equivalence relation
and the quotient is the set of these subsets.

Formally, given a set $A$ and an equivalence relation $\sim$ on $A$, the equivalence class for each $a \,\in A$ is,

\[
\class a = \{ b \in A \, \vert \, b \sim a \}
\]

The quotient set denoted as $\A/sim$ is the set of equivalence classes of $\sim$,


\[
\A/sim =\{[a] \in \wp(A) \, \vert \, a \in A\}
\]

%why quotients is useful?
There are many mathematical notions which can be constructed as
quotient sets. 
For example, the integers modulo some number
$n$ is the quotient set constructed by quotienting the set of all
integers $\Z$ with the congruence relation which equates two integers sharing the same remainders when divided by
$n$.
For another example, the set of rational numbers $\Q$ is defined as the set of numbers
which can be expressed as fractions, but different fractions like
$\frac{1}{2}$ and $\frac{2}{4}$ can be
reduced to the same rational number. 
In other words, $\Q$ can be constructed by quotienting the set of pairs of integers, while the
second is non-zero integer, with the equivalence
relation which equates fractions sharing the same irreducible forms.
A less common example is the set of integers $\Z$, which can also been
obtained from quotienting the set of pairs of natural numbers $\N \times \N$ which represent integers as the result of subtraction
between two natural numbers within each pair. Furthermore real
numbers can be represented by Cauchy sequences of
rational numbers, hence the set of real numbers $\R$ is the quotient
set of the set of Cauchy sequences of rational numbers with the
equivalence relation that the distance between two sequences converges
to zero. There are more examples of quotient sets, but the main
topic of this report is quotients in \emph{type theory}. 

\subsection{Type Theory}
\label{tt}

The theory of types was first introduced by Russell \cite{rus:1903} as
an alternative to naive set theory. Since then, mathematicians and
computer scientists have developed a number of variants of type
theory. The type theory in this discourse is the one developed by Per
Martin-L\"{o}f \cite{per:71,per:82} which is also called
intuitionistic type theory. It is based on the Curry-Howard
isomorphism between propositions and the types of its proofs such that
it can served as a formalisation of mathematics. For a detailed
introduction, refer to \cite{nor:00}.

Per Martin-L\"{o}f proposed both an intensional and an extensional
variants of his intuitionistic type theory. The distinction between them is whether definitional equality is distinguished from
propositional equality. In \itt{}, definitional equality exists
between two definitionally identical objects, but propositional
equality is a type which requires proof terms. Anything is only
definitionally equal to itself and all terms that can be normalised to
it, which means that definitional equality is decidable in
\itt{}.
Therefore type checking that depends on definitional equality is decidable as well~\cite{alt:99}
. 
The type for propositional equality in \itt{} is usually written as
$Id(A,a,b)$ (which is also called
\emph{intensional equality} \cite{nor:90}). 
In Agda\cite{norell:09}, an implementation of \itt{},  it is written
as |a ≡ b| with the type |A| often kept implicit. 
This set has an unique element |refl| only if |a| and |b| are
definitionally equal and is uninhabited if not. 
However in \ett{}, the two kinds of equalities are not distinguished, so if we have $p \,\colon Eq
(A,a,b)$ (which is called extensional equality \cite{nor:90}), $a$ and $b$ are
definitionally equal. 
It means that terms which have different normal forms may be definitionally equal. In other words, definitional equality is
undecidable and type checking becomes undecidable as well. However
Altenkirch and McBride have introduced a variant of \ett{} called
\emph{Observational Type Theory}  \cite{alt:06} in which definitional equality is
decidable and propositional equality is extensional.

%The propositional equality in \ett{} is written as $Eq(A,a,b)$ and is
%also \emph{extensional equality}. \todo{Why?}


% There are also two different propositions expressing the equality
% between two elements in Type Theory \cite{nor:90}. Both of them
% require the types of two elements are definitionally equal.
% One is intensional equality written as $Id(A,a,b)$ and it is inhabited
% only we have a proof showing $a$ and $b$ are definitionally equal. The
% other is extensional equality written as $Eq(A,a,b)$, the elements
% do not depend on an element of $A$ and the largest difference is if
% $Eq(A,a,b)$ is inhabited, then $a$ converts to $b$ and vice versa. The
% latter one will make type-checking undecidable so we usually use the
% first one which is available in \itt{}. For example in Agda,


Type theory can also serve as a programming language in
which the evaluation of a well-typed program always terminates
\cite{nor:90}. 
There are various implementations based on different type theories, such as
NuPRL, LEGO, Coq, Epigram and Agda.
%\todo{Possibly a separate section (maybe one page) for Agda} 
Agda is one of the most recent implementations of intensional version
of \mltt{}. 
It is a dependently typed programming language, we can write program specifications as
types. 
As we have seen, \mltt{} is based on the Curry-Howard
isomorphism: types are identified with propositions and programs (or
terms) are identified with proofs. 
Therefore it is not only a programming language but also a
theorem prover which allows user to verify Agda programs in
itself. 
Compared to other implementations, it has a package of useful
features such as pattern matching, unicode input, and implicit
arguments \cite{bov:09}, but it does not have tactics and consequently
its proofs are less readable than implementations that do. Since this project is based on \mltt{}, it is a good choice to implement our definitions
and verify our theorems and properties in Agda.  For a detailed
introduction of Agda, refer to \cite{norell:09}.

To move from set theory to type theory, the similarities and differences should be made clear. Although type theory has some similarities to set theory, their foundations are different. Types play a similar role to sets and they are
also called sets in many situations. However we can only create
elements after we declare their types, while in set theory elements exist there before
we have sets. For example,
we have the type $\N$ for natural numbers corresponding to the set of
natural numbers in set theory. In set theory, $2$ is a shared element
of the set of natural numbers and the set of integers. While in type
theory, $\N$ provides us two constructors
$zero \,\colon\N$ and $suc\,\colon\N\to\N$, and $2$ can be constructed
as $suc\,(suc\,\,zero)$ which is of type $\N$ and does not have any other
types like $\Z$. Because different sets may contain the same elements, we
have the subset relation such that we can construct equivalence
classes and quotient set. 
In type theory we have to give constructors for any type before we can construct elements, which is different to the situation in set theory that
elements exist before we construct quotient sets. Therefore this approach to construct quotients in set
theory has some problems in type theory. In fact, Voevodsky constructs
quotients using this approach in Homotopy Type Theory using Coq
\cite{voe:hset} but here we
mainly discuss how to reinterpret quotient sets in the current settings of \itt{} (e.g. Agda).


\subsection{Quotient Types}

Following the correspondence between sets and types, many notions from
set theory can be reinterpreted in type theory. The product of
sets can be formed by $\Sigma$-Types and the functions can be
formed by $\Pi$-Types \cite{nor:00}.

However, in \itt{} a general approach to construct quotient types is
still unavailable. 

Alternatively, in \itt{}, we have \emph{setoids} which contain all the ingredients of quotients as follows,

\begin{definition}
A setoid $(A,\sim)\,\colon\Set_1$ is a set \footnote{Setoid could be universe polymorphic.} 
$A\,\colon\Set$ equipped with an equivalence relation ${\,\sim\,}\colon A \to A \to \Prop$.
\end{definition}

Here we assume $\Set$ means type, and for any $P \colon\,\Prop$, it has
at most one element, namely we can get proof irrelevance for
propositions which has type $\Prop$. In Agda, we define a setoid as

\begin{code}
{-
record Setoid : Set₁ where
  field
    Carrier           : Set
    _≈_                : Carrier → Carrier → Set
    isEquivalence : IsEquivalence _≈_
-}
\end{code}

It contains |Carrier| for an underlying set, |_≈_| \footnote{|_| mark the spaces for the explicit arguments in non-prefix operators} for a binary
relation on |Carrier| and a proof that it is an equivalence relation.

We can use setoids to represent quotients, just as we can represent
$4$ by the pair $(8,2)$. However there are several problems if we use
this approach. Firstly |Setoid| are
different from sets so that we have to redefine all the operations on
|Set|. An interesting problem is how to represent quotients if the base
type $A$ is already a setoid. Setoids are also unsafe because we have access to the underlying
 sets \cite{aan}. 
It is better that if the base type $A$ is of type $\Set$ then the type of
quotient derived from it and its equivalence relation should also be
of type $\Set$, just as if we divide $8$ by $2$ we prefer $4$ than
$(8,2)$. From mathematical perspective, we can find the structure of the base object is usually the same as the
structure of the resultant quotient object. So what could be a quotient type?

Here we firstly describe what quotient types are. Given a setoid
$(A,\sim)\,\colon\Set_1$, a type $Q : \Set$ is called the quotient
type of this setoid, if we can prove it implements the quotient set
$A/\sim$, no matter how we construct it.

For instance, since integers represent the result of subtraction of
any pairs of natural numbers, we can represent integers by the setoid $(\N\times\N , \sim)$ where $\sim$ is
defined as (more details in section~\ref{sec:definitions} on page~\pageref{sec:definitions})

\[(a , b) \sim (c , d) \defi  a + d \equiv c + b \]

$\sim$ can also be proved to be an equivalence relation. However the
set of integers $\Z\,\colon\Set$ can also be constructed as

The type $\Z\,\colon\Set$  is just the quotient type corresponding to
the setoid  $(\N\times\N , \sim)$. 

Quotient types have uses beyond encoding mathematical quotients. It is a type theoretical notion which means some notions in Type
Theory or in programming languages can also be treated as quotient
types. For example partiality monad divided by a weak
similarity ignoring finite delays \cite{aan}, propositions quotiented by
logical equivalence relation $\iff$  or the set of extensionally equal functions. Also
set-theoretical finite sets can be implemented as the quotient of
lists in Type Theory. 
Furthermore given any function $f \,\colon\, A \to B$, we obtain an
equivalence relation $\sim \,\colon A \to A \to \Prop$ called \emph{kernel}
of $f$ which is defined as $a \sim b \defi f \,a \equiv f \,b$. Based on
this setoid $(A,\sim)$ we can form a quotient.
Indeed any type can be seen as quotient types of itself with the
intensional equality |≡|.

%How to obtain quotient type? 

In the definition of quotient types, we do not provide an approach to
construct them from given setoids. Indeed how to obtain a
quotient type of a given setoid is one of the main topics of this
project.

One feasible approach in current setting of \itt{} is to manually construct
the quotient type as we do in the example of the set of integer above,
and prove it is the required quotient type. We can form a quotient
using the quotient interfaces introduced in
\cite{aan}, which require the necessary proofs for some type $Q : \Set$ to be
the quotient type of some setoid $(A , \sim)$. These proofs are also
the basic properties of quotients, so we can use them to lift operations and prove some
general theorems. However, this approach is
inefficient because the quotient types and the properties have to be
manually figured out rather than automatically derived. 
%The lifting of functions also  proofs that these functions or
%predicates respect the equivalence relation\cite{hof:95:sm}.
Furthermore, some quotients like real numbers are undefinable even
though we can define the base type and equivalence relation for them
\cite{nuo:10} . Although it has some drawbacks, it is feasible without
extending \itt{} and it provides some convenience in practice. There
have been some results on this \cite{aan}, which I will discuss them
in section~\ref{sec:definitions}. 

%In this report, I will use the symbol $\A/sim$ for the quotient based
%on a given setoid  $(A,\sim)$. 
%To make the difference between setoids and quotient types clear, we
%use an analogy, $8\div2=4$. The number 4 is the quotient because $4
%\times 2 = 8$, and we cannot recover the dividend and the divisor
%from the quotient $4$ or manipulate $8$ or $2$ separately. Similarly,
%setoids contain pairs of dividend and divisor, but quotient sets do
%not include all the information from the setoids. Furthermore one set can be the quotient sets of several different setoids. 

The ideal approach should be an axiomatised type former for quotient
types. It means that we have to extend \itt{} with the introduction
rules and elimination rules of quotient types. However there are
many problems arising, for example the constructors for quotient types, the
definitional equality of quotient types etc.
% As we have seen before, all types in \itt{} can be seen as quotient
% types while the equivalence relation is the identity relation. Based
% on this idea, new quotient types can be seen as replacing the
% underlying equivalence relation with new one. In \itt{}, type checking which depends on definitional
% equality does not identify propositionally equal terms such that the
% new quotient type fails to work as $\Set$. 

Quotient types can be seen as the result of replacing the equivalence
relation of given types. This operation does not work in \itt{}, but it seems
easier to manage in \ett{} where
propositional equal terms are also definitionally equal. Nevertheless there
are still some problems which we discuss in the literature review.

%[(S m) , (S p)] -> [m , p] 
%[(S(S(S m))) , m] -> [(S(S(S m))) m] 
%Vec (S m + n) = Vec S (m + n).

%  In this way, the constructors for quotient
% type are automatically generated which means we have to use the
% constructors for base type with some symbols to represent the
% corresponding element in quotient type. Because of that, each element
% of quotient type sometimes has more than one normal forms which are not
% $\beta$-equivalent terms. As a result, the different representations
% for the same term of quotient type are only propositionally equal with
% respect to the equivalence relation rather than definitionally equal. 
%Therefore it still remains a difficult problem in \itt{}.
% Maybe we can write some new beta-conversion rules for quotient
% types, then different terms maybe definitionally equal to each other.




% \subsection{The relation between equality and quotient types}



\subsection{Functional extensionality and quotient types}

As we have mentioned before, in \itt{} propositional equality $Id(A,a,b)$ is inhabited
if and only if $a$ and $b$ are definitionally equal terms. The Agda
definition could be written as

\begin{code}

data Id (A : Set) : A → A → Set where
  refl : (a : A) → Id A a a

\end{code}

However the equality of functions are not only judged  by
definitions. Functions are
usually viewed extensionally as black boxes. If two functions pointwise
generate the same outputs for the same inputs, they are equivalent
even though their definitions may differ. This is called
functional extensionality which is not inhabited \cite{alt:99} in original
\itt{} and can be expressed as following,

given two types $A$ and $B$, and two functions $f,\,g\,\colon A \to B$,

\[Ext = \forall\, x\colon A, f x = g x \to f = g\]

The problem seems easy to solve by just adding a constant $ext : Ext$
to \itt{} as following codes in Agda

\begin{code}

postulate
  ext : {A : Set}{B : A → Set}{f g : (x : A) → B x}
        → ((x : A) → Id (B x) (f x) (g x)) 
        → Id ((x : A) → B x) f g

\end{code}

However, postulating something could lead to inconsistence. If we
postulate $Ext$, then theory is no longer adequate, which means it is possible to define irreducible terms. 
It can be easily verified in Agda through formalising a non-canonical
term for a natural number by an eliminator of intensional equality. 

Using the eliminator |J| \footnote{It is originally
  used by Martin-L\"{o}f \cite{nor:90} and a good explanation could be
found in \cite{ngk:11}}  of the |Id A a b| :

\begin{code}

J : (A : Set)(P : (a b : A) → Id A a b → Set)
    → ((a : A) → P a a (refl a))
    → (a b : A)(p : Id A a b) → P a b p
J A P m .b b (refl .b) = m b

\end{code}
we can construct an irreducible term of natural number as
\begin{code}

irr : ℕ
irr = J (ℕ → ℕ) (λ f g P → ℕ) (λ f → 0) (λ x → x) (λ x → x) (ext refl)

\end{code}

With this term, we can construct irreducible terms of any type |A| by a
mapping |f : ℕ → A|. This will destroy some good features of \itt{}
since it could leads to nonterminating programs.

Altenkirch investigates this issue and gives a solution in
\cite{alt:99}. He proposes an extension of \itt{} by a universe of
propositions $\Prop$ in which all proofs of same propositions are
definitionally equal, namely the theory is proof irrelevant. At the same time,
a setoid model where types are interpreted by a type and an equivalence relation acts as the metatheory and $\eta$-rules for
$\Pi$-types and $\Sigma$-types hold in the metatheory. The extended type
theory generated from the metatheory is decidable and adequate, $Ext$ is
inhabited and it permits large elimination (defining a dependent type by recursion). Within this type theory,
introduction of quotient types is straightforward. 
The set of functions are naturally quotient types, the hidden information is the
definition of the functions and the equivalence relation is the
functional extensionality.
% extension

There are more problems concerning quotient types and most
of them are related to equality. One of the main problems is how to lift the functions for
base types to the ones for quotient types. Only functions respecting the
equivalence relation can be lifted. Even in \ett{}, the implementation
of quotient types does not stop at replacing equality of the types. We
will discuss these in next section.

\section{Literature Review}
\label{sec:lr}

% 1. Why I mention about this article?
% 2. More description about these articles  in a more comprehensive
% way (tell a story)
% compare and link between literatures

In \cite{cab}, Mendler et al. have firstly considered building new types from a
given type using a quotient operator $//$. Their work is based on an
implementation of \ett{}, NuPRL. In NuPRL, every type
comes with its own equality relation, so the quotient operator can be
seen as a way of redefining equality in a type. But it is not all
about building new types. They also discuss problems that arise from
defining functions on the new type which can be illustrated using a simple example. 

Assume the base type is $A$ and the new equivalence relation is $E$, the new
type can be formed as $A//E$. 

When we want to define a function $f \,\colon\, A//E \to Bool$,  $f\,a \not= f\,b$ may
exists for $a, b \,\colon A$ such that $E\,a\,b$. This will lead to
inconsistency since $E\,a\,b$ implies $a$ converts to $b$ in \ett{}, hence
the left hand side $f\,a$ can be converted to $f\,b$, namely we get $f\,b \not= f\,b$
which is contradicted with the equality reflection rule. 

Therefore a function is said to be well-defined \cite{cab} on the new type only
if it respects the equivalence relation $E$, namely

$$\forall \, a\,b\,\colon A, E\,a\,b \to f\,a = f\,b$$

We call this \emph{soundness} property in \cite{aan}.

 After the introduction of quotient types, Mendler further investigates
 this topic from a categorical perspective in ~\cite{men:90}. He uses
 the correspondence between quotient types in \mltt{} and coequalizers
 in a category of types to define a notion called \emph{squash types},
 which is further discussed by Nogin \cite{nog:02}.

To add quotient types to \mltt{}, Hofmann proposes  three models for
quotient types in his PhD thesis \cite{hof:phd}. The first one is a setoid model for
quotient types. In this model all types are attached with partial
equivalence relations, namely all types are setoids rather than
sets. Types without a specific equivalence relation can be seen as
setoids with the basic intensional equality. This is similar to
\ett{} in some sense. The second one is groupoid model which solves some problems
but it is not definable in \itt{}. He also proposes a third model to
combine the advantages of the first two models, but it also has some
disadvantages. Later in \cite{hof:95:sm} he gives a simple model in which we have type dependency only at the propositional level, he also shows that extensional Type Theory is conservative over \itt {}  extended with quotient types and a universe \cite{hof:95:con}.

Nogin \cite{nog:02} considers a modular approach to axiomatizing the
same quotient types in NuPRL as well. Despite the ease of constructing new types
from base types, he also discusses some
problems about quotient types. For example, since the equality is
extensional, we cannot recover the
witness of the equality.  He suggests including more axioms to
conceptualise quotients. He decomposes the formalisation of quotient type
into several smaller primitives such that they can be handled much
simpler.

Homeier \cite{hom} axiomatises quotient types in Higher Order Logic
(HOL), which is also a theorem prover. He creates a tool package to
construct quotient types as a conservative extension of HOL such that
users are able to define new types in HOL. Next he defines the
normalisation functions and proves several properties of
these. Finally he discussed the issues when quotienting on the
aggregate types such as lists and pairs.


Courtieu \cite{cou:01} shows an extension of Calculus of Inductive Constructions
with \emph{Normalised Types} which are similar to quotient types, but equivalence relations are replaced by normalisation functions. 
However not all quotient types have normal forms. Normalised types are
proper subsets of quotient types, because we can easily recover a quotient
type from a normalised type as below
\[ (A, Q, \class\dotph \colon A \to Q) \Rightarrow(A, \lambda \,a \,b\to \class a = \class b)\]


Barthe and Geuvers \cite{bar:96} also propose a new notion called
\emph{congruence types}, which is also a special class of quotient
types, in which the base type are inductively defined and with a set
of reduction rules called the term-rewriting system. The idea behind
it is the $\beta$-equivalence is replaced by a set of
$\beta$-conversion rules. Congruence types can be treated as an
alternative to the pattern matching introduced in \cite{coq:92}. The main
purpose of introducing congruence types is to solve problems in
term rewriting systems rather than to implement quotient types.


Barthe and Capretta \cite{bar:03} compare different ways to setoids in type theory.
The setoid is classified as partial setoid or total setoid depending
on whether the equality relation is reflexive or not. They also
consider obtain quotients with different kinds of setoids, especially
the ones from partial setoids are difficult to define because the lack
of reflexivity.

Abbott, Altenkirch et al. \cite{abb:04} provides the basis for
programming with quotient datatypes polymorphically based on their
works on containers which are datatypes whose instances are
collections of objects, such as arrays, trees and so on. Generalising
the notion of container, they define quotient containers as the
containers quotiented by a collection of isomorphisms on the positions
within the containers.

Voevodsky \cite{voe:hset} implements quotients in Coq based on a set
of axioms of Homotopy Type Theory. It is based on the groupoid model
for \itt{} where isomorphisms are equalities. He firstly implement
equivalence class and use it to implement quotients which is an
analogy to the construction of quotient sets in set theory. 

\section{Aims and Objectives of the Project}
\label{sec:ob}

As we have seen, quotients can enable defining or constructing various kinds of
mathematical notions or programming datatypes, thus the introduction of
quotient types will be quite beneficial in theorem provers and
programming languages based on Type Theory. 

The objective of this project is to investigate and explore the ways of
implementing quotients in \mltt{}, especially in intensional
variant where type checking always terminates.


The project will be undertaken step by step. Firstly, we should make
the basic notions clear, for example what are quotients and if we want
quotients in type theory what kind of problems need to be solved. We
also need to do research on related works on this topic as much as
possible.

The second step is to work in the current setting of \itt{},
investigating some definable quotients, and building the module structure of quotients. The module structure
and some research on definable quotients has been done in
\cite{aan}.

Next we need to investigate some undefinable quotients such as the set
of real numbers $\R$ and partiality monads and prove why they are undefinable. The
key different characters between definable and undefinable quotients
will be studied. A proof of why $\R$ is undefinable is also given in
\cite{aan}.

The development of framework of quotient types in \itt{} is one of the major
objectives. We need to propose a set of rules to axiomatise quotient
types in \itt{}. To test our approach with a few typical quotients
to explore its potential benefits. It is better if we could
constructed quotients in a general way and the quotient types have
useful properties that facilitating programming and reasoning.
The correctness of axiomatisation
and the consistency of extended \itt{} require formal proofs.


The ultimate aim is to extend \itt{} such that all quotients can be
defined and handled easily and correctly without losing the consistency
and features of \itt{}.

Finally, we will summarise all these works, including background
information, literature review, defining quotient types in
\itt{}, the benefits of it and the application of it into a PhD Thesis.


%\subsection{Theoretical Methods}

To do this research, we need to review and compare
the existing approaches in different implementations of \mltt{},
and try to determine the best approach by testing it in real cases.

As we have mentioned before, Agda is a good implementation of
\itt{}. Conducting this research in Agda will be useful as we can verify our proofs in it and try to apply quotient types
to a lot of practical examples.

We also need to advertise our work, get feedback from the users, and
improve our approaches such that they are more applicable and easier
to use.


\section{Results and Discussion}
\label{sec:rd}

\subsection{Definitions}
\label{sec:definitions}

Currently, we are on the first stage and there is some progression on
definable quotients in \itt{} \cite{aan}. Here I will present some necessary knowledge from that paper.

%It is about the definable quotients and some undefinable
%quotients. Here we only talk about the quotient set, but it is
%universal polymorphic. 

During the first stage, the aim is to explore the potential to define quotients
in current setting of \itt{}. 


Given a setoid $(A,\sim)$, we know what is a quotient type but we cannot define it from the setoid because there are no axiomatised quotient
types. We can only prove some type is a quotient type of a given
setoid. Therefore the only way to introduce possible quotient types $Q
\,\colon \Set$ is to define it by ourselves. With defined $Q$ and
$(A,\sim)$, we are required construct some structures of quotients in
\cite{aan} which consists of a set of essential properties of quotients.

Here I will explain these structures by using the example of integers
in Agda. All integers are the result of subtraction between two
natural numbers. Therefore we can use a pair of natural numbers in a subtraction
expression to represent the resulting integer.
For example, $1 - 4 = - 3$ says that the pair of natural numbers $(1,4)$
represents the integer $- 3$. Assuming we have the necessary definitions
of natural numbers, the base type of this quotient is:

$$\Z_0=\N \times \N$$

Mathematically we know that for any two pairs of natural numbers $(n_1, n_2)$ and $(n_3, n_4)$, 
$$ n_1 - n_2 = n_3 - n_4\iff n_1 + n_4 = n_3 + n_2$$

Because the results of subtraction are the same, we can infer that the
two pairs represent the same integer, so the equivalence relation
$\sim$ for $\Z_0$ could be defined as

\begin{code}
{-
_∼_ : Rel ℤ₀
(n1 , n2) ∼ (n3 , n4) = (n1 + n4) ≡ (n3 + n2)

\end{code}

Here |≡| is propositional equality. Of course we must prove |∼| is an
equivalence relation then we can define the setoid $(\Z_0,\sim)$ in
Agda as\footnote{the proof |_∼_isEquivalence| is omitted here}

\begin{code}

ℤ-Setoid : Setoid
ℤ-Setoid = record
  { Carrier           = ℤ₀
  ; _≈_                = _∼_
  ; isEquivalence = _∼_isEquivalence
  }

\end{code}

In set theory, we can immediately derive the quotient set from this
setoid which is the set of integers $\Z$, but in current setting of \itt{},
we need to define $\Z$ as follows

\begin{code}

data ℤ : Set where
  +_    : (n : ℕ) → ℤ
  -suc_ : (n : ℕ) → ℤ

\end{code}

This is called normal form or canonical form of integers.

The next step is to prove that it is the quotient type of the setoid $(\Z_0,\sim)$.
To relate the setoid and the potential quotient type, we need to
provide a mapping function from the base type $\Z_0$ to the target
type $\Z$ which should be the normalisation function

\begin{code}

[_]                     : ℤ₀ → ℤ
[ m , 0 ]             = + m
[ 0 , suc n ]        = -suc n
[ suc m , suc n ] = [ m , n ]

\end{code}

The first property to prove is the \emph{sound} property,

\begin{code}

sound                      : ∀ {x y} → x ∼ y → [ x ] ≡ [ y ]

\end{code}

The normalised results of two propositional equal elements of $\Z_0$
should be the same. With this property, we are able to form a prequotient which is defined as


\begin{code}

record PreQu (S : Setoid) : Set₁ where
  constructor
    Q:_[]:_sound:_
  private
    A    = Carrier S
    _∼_ = _≈_ S
  field
    Q       : Set
    [_]      : A → Q
    sound : ∀ {a b : A} → a ∼ b → [ a ] ≡ [ b ]
-}
\end{code}

and the prequotient of integers is,

\begin{code}
{-
ℤ-PreQu : PreQu ℤ-Setoid
ℤ-PreQu = record
  { Q       = ℤ
  ; [_]     = [_]
  ; sound   = sound
  }
-}

\end{code}

To form quotients we have several different definitions as written in \cite{aan},

\begin{enumerate}

\item \emph{Quotient with a dependent eliminator}

\begin{code}
{-
record Qu {S : Setoid} (PQ : PreQu S) : Set₁ where
  private 
    A       = Carrier S
    _∼_    = _≈_ S
    Q       = Q' PQ
    [_]     = nf PQ
    sound : ∀{a b : A} → (a ∼ b) → [ a ] ≡ [ b ]
    sound = sound' PQ
  field
    qelim   : {B : Q → Set}
            → (f : (a : A) → B [ a ])
            → ((a b : A) → (p : a ∼ b) 
            → subst B (sound p) (f a) ≡ f b)
            → (q : Q) → B q
    qelim-β : ∀ {B a f} q → qelim {B} f q [ a ]  ≡ f a
-}
\end{code}


\item \emph{Exact (or efficient) quotient}

\begin{code}
{-
record QuE {S : Setoid}{PQ : PreQu S}(QU : Qu PQ) : Set₁ where
  private 
    A       = Carrier S
    _∼_    = _≈_ S
    [_]     = nf PQ
  field
    exact : ∀ {a b : A} → [ a ] ≡ [ b ] → a ∼ b
-}
\end{code}

\item \emph{Quotient with a non-dependent eliminator and induction principle}

\begin{code}
{-
record QuH {S : Setoid} (PQ : PreQu S) : Set₁ where
  private 
    A     = Carrier S
    _∼_  = _≈_ S
    Q    = Q' PQ
    [_]   = nf PQ
  field
    lift    : {B : Set}(f : A → B) 
           → ((a b : A) → (a ∼ b) → f a  ≡ f b) 
           → Q → B
    lift-β : ∀ {B a f q} → lift {B} f q [ a ]  ≡ f a
    qind : (P : Q → Set)  
           → (∀ x → (p p' : P x) → p ≡ p')
           → (∀ a → P [ a ]) 
           → (∀ x → P x)
-}
\end{code}

\item \emph{Definable quotient}
 
\begin{code}
{-
record QuD {S : Setoid}(PQ : PreQu S) : Set₁ where
  constructor
    emb:_complete:_stable:_
  private 
    A     = Carrier S
    _∼_  = _≈_ S
    Q     = Q' PQ
    [_]   = nf PQ
  field
    emb        : Q → A
    complete : ∀ a → emb [ a ] ∼ a
    stable      : ∀ q → [ emb q ] ≡ q

\end{code}

\end{enumerate}

We have proved that the first and third definitions are equivalent and
the last one is the most strongest definition which can generate any
other from it \cite{aan}.

For integers, it is natural to define a function to choose a representative for each element in $\Z$,

\begin{code}

⌜_⌝            : ℤ → ℤ₀
⌜ + n ⌝      = n , 0
⌜ -suc n ⌝  = 0 , suc n

\end{code}

Now we need to prove |⌜_⌝| is the required embedding function, namely
it is the inverse function of |[_]|.

Firstly |⌜_⌝| is left inverse of |[_]|,

\begin{code}

compl                            : ∀ {n} → ⌜ [ n ] ⌝ ∼ n
-}
\end{code}

This is called the \emph{complete} property. 

Secondly |⌜_⌝| is right inverse of |[_]|,

\begin{code}
{-
stable                : ∀ {n} → [ ⌜ n ⌝ ] ≡ n
-}
\end{code}

This is called the \emph{stable} property.

Now we can form the definable quotient structure with the prequotient we have,

\begin{code}
{-
ℤ-QuD : QuD ℤ-PreQu
ℤ-QuD = record
  { emb         = ⌜_⌝
  ; complete  = λ z → compl {z}
  ; stable        = λ z → stable {z}
  } 
-}
\end{code}

Now we have the mapping between the base type $\Z_0$ and the target type $\Z$, and have proved that |[_]| is a normalisation function.

We can obtain the dependent and non-dependent eliminators by translating the definable quotient into other definitions,

\begin{code}
{-
ℤ-Qu  = QuD→Qu ℤ-QuD

ℤ-QuE = QuD→QuE {_} {_} {ℤ-Qu} ℤ-QuD

ℤ-QuH = QuD→QuH ℤ-QuD 
-}
\end{code}

We can benefit from the interaction between setoids and quotient types
in a number of ways.

Firstly the setoid definitions are usually simpler than the normal
definitions. In the case of integers, the normal form have two
constructors. For propositions with only one argument, sometimes we
have to prove them for both cases in the canonical definition. With
the increasing number of arguments in propositions, the number of
cases we need to prove would increase exponentially. A real case is
when trying to prove the distributivity of multiplication over
addition for integers: the large amount of cases makes the
proving cumbersome and we can hardly save any effort from any theorems
we proved. 
However for the setoid definition of integers, a
proposition can be converted into another proposition on natural
numbers which is much convenient to prove because we do not need to
prove case by case and we have a bundle of
theorems for natural numbers. For example,

\begin{code}
{-
distʳ : _*_ DistributesOverʳ _+_
distʳ (a , b) (c , d) (e , f) = ℕ.dist-lemʳ a b c d e f += ⟨  ℕ.dist-lemʳ b a c d e f ⟩
-}
\end{code}

Moreover, as we have constructed the semiring of natural numbers, it
is even simpler to use the automatic prover \emph{ring solver} to prove simple equation of natural numbers. 

The rest we have to do is to lift the properties proved for setoid definition to the ones for canonical definition.
We can easily lift n-ary operators defined for $\Z_0$ to the ones for $\Z$ by

\begin{code}
{-
liftOp                  : ∀ n → Op n ℤ₀ → Op n ℤ
liftOp 0 op         = [ op ]
liftOp (suc n) op = λ x → liftOp n (op ⌜ x ⌝)
-}
\end{code}

However, this lift function is unsafe because some operations on
$\N\times\N$ do not make sense when applying this function. It is
similar to the situation when defining functions on types with
replaced equality in \ett{}. The solution is to lift functions which
respects the equivalence relation. I only define the two most commonly
used safe lifting functions

\small
{\begin{code}
{-
liftOp1s : (f : Op₁ ℤ₀) → (∀ {a b} → a ∼ b → f a ∼ f b) → Op₁ ℤ
liftOp1s f cong = λ n → [ f ⌜ n ⌝ ]

liftOp2s : (* : Op₂ ℤ₀) → (∀ {a b c d} → a ∼ b → c ∼ d → * a c ∼ * b d) → Op₂ ℤ
liftOp2s _op_ cong = λ m n → [ ⌜ m ⌝ op ⌜ n ⌝ ]
-}
\end{code}}

Then we can obtain the $\beta$-laws which are very useful,

\begin{code}
{-
liftOp1-β : (f : Op 1 ℤ₀) → (cong : ∀ {a b} → a ∼ b → f a ∼ f b) → 
              ∀ n → liftOp1safe f cong [ n ] ≡ [ f n ]


liftOp2-β : (op : Op 2 ℤ₀) → (cong : ∀ {a b c d} → a ∼ b → c ∼ d → op a c ∼ op b d) →
              ∀ m n → liftOp2safe op cong [ m ] [ n ] ≡ [ op m n ] 
-}
\end{code}

Now we can lift the negation easily

\begin{code}
{-
-_ : Op 1 ℤ
-_ = liftOp1safe ℤ₀.-_ ℤ₀.⁻¹-cong

\end{code}

and the $\beta$-laws for negation can be proved as

\begin{code}

-β : ∀ a → - [ a ] ≡ [ ℤ₀- a ]
-β = liftOp1-β ℤ₀-_ ℤ₀.⁻¹-cong

\end{code}

When trying to prove theorems for canonical integers, we can lift
proved properties for the setoid integers, such as commutativity of
any binary operations,

\begin{code}

liftComm : ∀ {op : Op 2 ℤ₀} → P.Commutative _∼_ op → Commutative (liftOp 2 op)
liftComm {op} comm x y = sound (comm ⌜ x ⌝ ⌜ y ⌝)

\end{code}

The generalised lifting function for commutativity is also one of the
derived theorem of quotients as it only uses |sound| and |⌜_⌝| which are part of the
quotients. We can then lift the commutativity of addition and multiplication,

\begin{code}

+-comm : Commutative _+_
+-comm = liftComm ℤ₀.+-comm

*-comm :  Commutative _*_
*-comm = liftComm ℤ₀.*-comm

\end{code}

It is also much simpler and reasonable to prove the complicated distributivity of multiplication over addition, 

\begin{code}

distʳ : _*_ DistributesOverʳ _+_
distʳ a b c = sound  (ℤ₀.*-cong (compl {⌜ b ⌝ + ⌜ c ⌝}) zrefl >∼< 
              ℤ₀.distʳ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ >∼<
              ℤ₀.+-cong compl' compl')
-}
\end{code}

There is no need to use pattern matching, namely prove the
propositions inductively. At first, I tried to prove distributivity by
case analysis, and I found it is especially difficult and the proof is
too long and it looks like (I omit to write the long proof for each clause):

\begin{code}

{-
distʳ : _*_ DistributesOverʳ _+_
distʳ (+ n) (+ n') (+ n0) = ...
distʳ (+ n) (+ n') (-suc n0) = ...
distʳ (+ n) (-suc n') (+ n0) = ...
distʳ (+ n) (-suc n') (-suc n0) = ...
distʳ (-suc n) (+ n') (+ n0) = ...
distʳ (-suc n) (+ n') (-suc n0) = ...
distʳ (-suc n) (-suc n') (+ n0) = ...
distʳ (-suc n) (-suc n') (-suc n0) = ...
-}

\end{code}

Even though it is provable in this way, it is not the best choice
to prove something like distributivity by induction.

 The simplicity of the short proof is achieved by
applying the quotient properties such as |sound|, we can translate or
convert the proposition into the corresponding proposition for setoid
integers. Although all the lemmas may be as much as the long proofs by
induction, they are more meaningful and can be reused. We can further
translating the propositions for setoid integers into some easier
propositions for natural numbers. 
The connections between canonical integers and natural numbers is built by
the definition of quotient.

We can also lift a structure of properties such as monoid,

\begin{code}
{-

liftId : ∀ {op : Op 2 ℤ₀}(e : ℤ) → Identity _∼_ ⌜ e ⌝ op → Identity e (liftOp 2 op)

liftAssoc : ∀ {op : Op 2 ℤ₀}(cong : Cong2 op) → Associative _∼_ op → 
                   Associative (liftOp2safe op cong)

liftMonoid : {op : Op 2 ℤ₀}{e : ℤ}(cong : Cong2 op) → IsMonoid _∼_ op ⌜ e ⌝ →
                    IsMonoid _≡_ (liftOp 2 op) e
-}

\end{code}

These lift functions for operators and properties can be generalised
even further such that they can be applied to all quotients that have
similar algebraic structures.
They are all derived theorems for quotients which can save a lot of work for
us. We can reuse them in the next example, the set of rational numbers $\Q$.

\subsection{Rational numbers}

The quotient of rational numbers is better known than the previous
quotient. We usually write two integers $m$ and $n$ ($n$ is not zero) in
fractional form $\frac{m}{n}$ to represent a rational number. Alternatively we
can use an integer and a positive natural number such that it is
simpler to exclude 0 in the denominator. Two fractions are equal if
they are reduced to the same irreducible term. If the numerator and
denominator of a fraction are coprime, it is said to be an irreducible
fraction. Based on this observation, it is naturally to form a definable quotient, where the base type is 

$$\Q_0 = \Z \times \N$$

The integer is \emph{numerator} and the natural number is \emph{denominator-1}. This approach avoids invalid fractions from construction. 

In Agda, to make the terms more meaningful we define it as

\begin{code}

data ℚ₀ : Set where
  _/suc_ : (n : ℤ) → (d : ℕ) → ℚ₀

\end{code}

In mathematics, to judge the equality of two fractions, it is easier to conduct the following conversion,

$$ \frac{a}{b} = \frac{c}{d} \iff a \times d = c \times b $$

Therefore the equivalence relation can be defined as,

\begin{code}

_∼_                                : Rel ℚ₀
(n1 /suc d1) ∼ (n2 /suc d2) =  n1 * suc d2 ≡ n2 * suc d1

\end{code}

The normal form of rational numbers, namely the quotient type in this quotient is the set of irreducible fractions. We only need to add a restriction that the numerator and denominator is coprime,

$$\Q = \Sigma (n \colon \Z). \Sigma (d \colon \N). \coprime \,n \,(d +1)$$

We can encode it using record type in Agda,

\begin{code}

record ℚ : Set where
  field
    numerator        : ℤ
    denominator-1 : ℕ
    isCoprime        : ? -- True (C.coprime? ∣ numerator ∣ (suc denominator-1))

\end{code}

The normalisation function is an implementation of the reducing
process, the |gcd| function which calculates the greatest common
divisor can help us reduce the fraction and give us the proof of coprime, 

\begin{code}

[_] : ℚ₀ → ℚ

\end{code}

\AgdaHide{
\begin{code}

[_] = ?

\end{code}
}

The embedding function is simple. We only need to forget the coprime proof in the normal form,

\begin{code}

⌜_⌝ : ℚ → ℚ₀
⌜ x ⌝ = (ℚ.numerator x) /suc (ℚ.denominator-1 x)

\end{code} 

Similarly, we are able to construct the setoid, the prequotient and
then the definable quotient of rational numbers. We can benefit from
the ease of defining operators and proving theorems on setoids while
still using the normal form of rational numbers, the lifted operators
and properties which are safer.


\subsection{Real numbers}

The previous quotient types are all definable in \itt{}, so we can
construct the definable quotients for them. However, there are some
types undefinable in \itt{}. The set of real numbers $\R$ has been proved to be undefinable in \cite{aan}.

We have several choices to represent real numbers. We choose Cauchy
sequences of rational numbers to represent real numbers \cite{bis:85}.

$$\R_{0} = \set{s : \N\to\Q \mid \forall\varepsilon
  :\Q,\varepsilon>0\to\exists m:\N, \forall i:\N, i>m\to \vert  s_i -
  s_m \vert  <\varepsilon}$$

We can implement it in Agda. First a sequence of elements of $A$ can be represented by a function from $\N$ to $A$:

\begin{code}

Seq     : (A : Set) → Set
Seq A = ℕ → A

\end{code}

And a sequence of rational numbers converges to zero can be expressed as follows:

\begin{code}

Converge    : Seq ℚ₀ → Set
Converge f = ∀ (ε : ℚ₀*) → ∃ λ lb → ∀ m n → ∣ (f (suc lb + m)) - (f (suc lb + n)) ∣ <' ε

\end{code}

Now we can write the Cauchy sequence of rational numbers:

\begin{code}

record ℝ₀ : Set where
  constructor f:_p:_
  field
    f : Seq ℚ₀
    p : Converge f

\end{code}

To complete the setoid for real numbers, an equivalence relation is required. In mathematics two Cauchy sequences $\R_0$ are said to be equal if their pointwise difference converges to zero,

$$r \sim s = \forall\varepsilon :\Q,\varepsilon>0\to\exists m:\N,
\forall i:\N, i>m\to \vert  r_i - s_i \vert <\varepsilon$$

The Agda version is in Appendix.

In set theory we can construct  quotient set $\R_0 /\sim$. However
since real numbers have no normal forms we cannot define the quotient
in \itt{}. Hence the definable quotient definition does not work for
it. The undefinability of any type $\R$ which is the quotient type
of the setoid $(\R_0, \sim)$ is proved by local continuity \cite{aan}.

\subsection{All epimorphisms are split epimorphisms}

In addition we have also prove that classically all epimorphisms are
split epimorphisms.

As we have mentioned above, Mendler \cite{men:90} has investigated
quotient types via coequalizers in category theory. We also explain
the correspondence in \cite{aan}. The coequalizer q
which corresponds to the function |[_]| in our quotient structures is an epimorphism.

According to the definition of epimorphisms, A morphism $e$ is an epimorphism if it is right-cancellative:

\begin{code}

Epi : {A B : Set} → (e : A → B) → (C : Set) → Set
Epi {A} {B} e C = ∀ (f g : B → C) → (∀ (a : A) → f (e a) ≡ g (e a)) → ∀ (b : B) → f b ≡ g b

\end{code}

If it has a right inverse it is called a split epi

\begin{code}

Split : {A B : Set} → (e : A → B) → Set
Split {A} {B} e = ∃ λ (s : B → A) → ∀ b → e (s b) ≡ b

\end{code}

We assume the axioms of classical logic

\begin{code}

postulate classic : (P : Set) → P ∨ (¬ P)

raa : {P : Set} → ¬ (¬ P) → P
raa {P} nnp with classic P
raa nnp | inl y = y
raa nnp | inr y with nnp y
... | ()

contrapositive : ∀ {P Q : Set} → (¬ Q → ¬ P) → P → Q
contrapositive nqnp p = raa (λ nq → nqnp nq p)

\end{code}

We also need one of the De Morgan's law in classical logic

\begin{code}

postulate DeMorgan : ∀ {A : Set}{P : A → Set} → ¬ (∀ (x : A) → P x) → ∃ λ (x : A) → ¬ P x

\end{code}

What we need to prove is

\begin{code}

Epi→Split : {A B : Set} → (e : A → B) → Set₁
Epi→Split e = ((C : Set) → Epi e C) → Split e

\end{code}

Because we have classical theorems, it is equivalent to prove the contrapositive of |Epi→Split|. To make the steps clear, we decompose the complicated proof. In order,
we postulate the following things first

\begin{code}

postulate A B : Set
postulate e : A → B

postulate ¬split : ¬ Split e

\end{code}

Now from the assumption that e is not a split, we can find an element $b : B$ which is not the image of any element $a : A$ under $e$

\begin{code}

¬surj : ∃ λ b → ¬ (∃ λ (a : A) → (e a ≡ b))
¬surj = DeMorgan (λ x → ¬split ((λ b → proj₁ (x b)) , λ b → (proj₂ (x b))))

b = proj₁ ¬surj

ignore : ∀ (a : A) → ¬ (e a ≡ b)
ignore a eq = proj₂ ¬surj (a , eq)

\end{code}

We can define a constant function

\begin{code}

f : B → Bool
f x = false

\end{code}

and postulate a function to decide whether $x : B$ is equal to b. The
reason to postulate it is we do not know the constructor of b and we
are sure that if $B$ is definable in Agda, the intensional equality
must be decidable.

\begin{code}

postulate g    : B → Bool
postulate gb  : g b ≡ true
postulate gb' : ∀ b' → ¬ (b' ≡ b) → false ≡ g b'

\end{code}

Finally we can prove $e$ is not an epi

\begin{code}

¬epiBool : ¬ Epi e Bool
¬epiBool epi with assoc (epi f g (λ a → gb' (e a) (ignore a)) b) gb
... | ()

¬epi : ¬ ((C : Set) → Epi e C) 
¬epi epi = ¬epiBool (epi Bool)

\end{code}

In \itt{}, if the quotient types are undefinable, we can not construct
the normalisation function |[_]|, and the proposition is
only proved to be true with classical axioms. Therefore it does not make
sense for the epimorphism from $\R_0$ to $\R$.

\section{Conclusion}
\label{sec:cl}

In the first phase of the project of quotient types in \itt{}, we
investigate the quotients which are definable in current setting of
\itt{}. Given some setoids, the corresponding quotient types are
separately defined and then proved to be correct by forming definable
quotients structure with the setoids. 
This approach provides us an alternative choice to define functions and
prove propositions. 
The properties contained in the quotient structure are very helpful in
lifting functions and propositions for setoids to quotient types. 
From the examples we have discussed, comparing manipulating quotient
types, it is probably simpler to define
functions on setoids and then we can lift functions and properties when they respect the equivalence relation.
However it is a little complicated to build the quotients and is only
applicable to quotients which are definable in current setting of \itt{}.

\subsection{Future work}

In next phase we will focus on the undefinable quotients (e.g. the set of real numbers) and
to implement undefinable quotients, extending \itt{} with axiomatised
quotient types is unavoidable. Although the definable quotients are
limited, it is still a good guide when axiomatising the quotient
types. The other quotient structures could also be applied to axiomatised
quotient types. To axiomatise quotient types we can refer to Martin
Hofmann's work in \cite{hof:phd}. we can implement and then extend his
work in Agda. We need to axiomatise the formation, introduction,
elimination rules for quotient types. After that we should be able to
define lifting function for quotient types. The properties of quotient
types should be proved and we should define some typical examples of
undefinable quotients and also definable ones. Moreover the other extensional
concepts such as proof irrelevance, functional extensionality and
propositional extensionality should be present. 

Additional future work could be to give a detailed proof of  the
conservativity of \ett{} over \itt{} with axiomatised quotient types extending the
work in \cite{hof:95:con}.  It means that the same types are inhabited
if they make sense in that type theory. To prove it, as he said, it is
enough that the type former of quotient types admits an action on
propositional isomorphisms. He also mentioned that he has shown this
in \cite{hof:phd} by adding quotient types and a universe, but the approach
to axiomatise quotient types is different. The proof of conservativity
is non-constructive because of the utilization of set-theoretic
quotienting and choice of representatives.

One area work is to extend the setoid model as metatheory
constructed by Altenkirch in \cite{alt:99} to
quotient types, and to find an approach to extend \itt{} without losing
nice features such as termination and decidable type
checking.
The basic idea of setoid model is to interpret all types as types with
equivalent relation, and since we have the proof-irrelevant universe
$\Prop$, the identity proof is unique. 
The extention of \itt{} with proof-irrelevant propositions and
$\eta$-rules as metatheory should be proved decidable, consistent and
adequate. Decidability of the type theory can be proved if definitional equality is decidable as we discussed
above. 
Consistency means there is no contradiction in a type theory, and it
should be provable using strong normalisation and Church-Rosser
theorem. 
Adequacy which has been mentioned above can be proved if there are no closed terms of type
$\N$ that are not reducible to numerals. 
As in \cite{alt:99}, the model employed is called \emph{categories with families} which
is introduced by Dybjer and Hofmann \cite{dyb:96,hof:97}.
To introduce the objective type theory, Altenkirch uses
an approach that is different to commonly used syntactical
approach. He define a model inside the metatheory and verify 
it is also decidable, consistent and adequate. We should follow a
similar approach to extend the model with quotient types. Recently
Agda has new a new feature called \emph{Dependent irrelevant function
  types} and it allows us to define the eliminator for the squash type
and it should be helpful for us to implement the proof-irrelevant
propositions in Agda.



Some other models, such as groupoid model
could also be investigated if we do not have proof irrelevance.
Voevodsky's construction of quotients in Homotopy Type
Theory can be found in\cite{voe:hset}. Since in Homotopy Type Theory,
two isomorphic objects are equal, the implementation of equivalent
classes should be possible and then the quotient types are natural to define.
However there are some problems of the definition: since 
the encoding is impredicative, the size problem will be present; the
properties of quotients are not provable. Nevertheless we can try to learn
from his construction and find out how it can fit into our work.

% pay attention to the connection,the flow of ideas throughout the article.
% one thing in one paragraph.



\newpage
\bibliography{quotients}
\bibliographystyle{plain}

%include Appendix.lagda

\end{document}
