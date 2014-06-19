\documentclass{sig-alternate}

% TeXSupport
\makeatletter
\def\doi#1{\gdef\@doi{#1}}\def\@doi{}
\toappear{\the\boilerplate\par{\confname{\the\conf}} \the\confinfo\par \the\copyrightetc.\ifx\@doi\@empty\else\par\@doi.\fi}
%\global\copyrightetc{Copyright \the\copyrtyr\ ACM \the\acmcopyr\ ...\$15.00}
\global\copyrightetc{ACM \the\acmcopyr\ ...\$15.00}

%% Below definition reduced the font size
%% of permission/copyright statement.  
%
\newfont{\mycrnotice}{ptmr8t at 7pt}
\newfont{\myconfname}{ptmri8t at 7pt}
\let\crnotice\mycrnotice%
\let\confname\myconfname%
\makeatother

\PassOptionsToPackage{utf8x}{inputenc}

\bibliographystyle{plain}

%agda literal file
\usepackage{agda}

\usepackage{dsfont}
%\let\proof\relax
%\let\endproof\relax
%\usepackage{amsthm}
\usepackage{relsize}
\usepackage{color}
\usepackage{amsmath}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{autofe}
\usepackage{stmaryrd}
\usepackage{textgreek}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{diagxy}

\usepackage{mypack}

\usepackage{url}

\usepackage[stable]{footmisc}

\usepackage[shortcuts]{extdash}


\begin{document}


% Permission Statement
\permission{Permission to make digital or hard copies of all or part of this work for personal or classroom use is granted without fee provided that copies are not made or distributed for profit or commercial advantage and that copies bear this notice and the full citation on the first page. Copyrights for components of this work owned by others than the author(s) must be honored. Abstracting with credit is permitted. To copy otherwise, or republish, to post on servers or to redistribute to lists, requires prior specific permission and/or a fee. Request permissions from Permissions@acm.org.}


% Conference Information
\conferenceinfo{LFMTP '14,}{July 17 2014, Vienna, Austria\\
Copyright is held by the owner/author(s). Publication rights licensed to ACM.}
\CopyrightYear{2014}
\crdata{978-1-4503-2817-3/14/07}

% DOI
\doi{http://dx.doi.org/10.1145/2631172.2631176}



\title{Some constructions on {\huge$\omega$}-groupoids \titlenote{This work is partially supported by Natural Science Foundation of China (Grant No. : 61070023) and Ningbo Natural Science Programme by Ningbo S\&T bureau (Grant No. : 2010A610104).}}

\numberofauthors{3}
\author{
% 1st. author
\alignauthor
Thorsten Altenkirch\\
       \affaddr{Computer Science}\\
       \affaddr{University of Nottingham}\\
       \email{txa@cs.nott.ac.uk}
% 2nd. author
\alignauthor
Nuo Li\\
       \affaddr{Computer Science}\\
       \affaddr{University of Nottingham}\\
       \email{nzl@cs.nott.ac.uk}
% 3rd. author
\alignauthor
Ond\v{r}ej Ryp\'a\v{c}ek\\
       \affaddr{University of Oxford}\\
       \affaddr{United Kingdom}\\
       \email{ondrej.rypacek@gmail.com}
}


\newcommand{\txa}[1]{\marginpar{txa:#1}}
\newcommand{\oxr}[1]{\marginpar{\footnotesize oxr:#1}}

\maketitle

\AgdaHide{
\begin{code}
{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check #-}


module BasicSyntax where 


open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product renaming (_,_ to _,,_)


infix 4 _≅_
infix 4 _=h_
infixl 6 _+T_ _+S_ _+tm_
infixl 5 _,_
infixl 7 _⊚_

\end{code}
}

\begin{abstract}

  Weak $\omega$-groupoids are the higher dimensional generalisation of
  setoids and are an essential ingredient of the constructive
  semantics of Homotopy Type Theory \cite{hott}.  Following up on our
  previous formalisation \cite{txa:csl} and Brunerie's notes
  \cite{gb:wog}, we present a new formalisation of the syntax of weak
  $\omega$-groupoids in Agda using heterogeneous equality. We show how
  to recover basic constructions on $\omega$-groupoids using
  suspension and replacement. In particular we show that any type
  forms a groupoid and we outline how to derive higher dimensional
  composition. We present a possible semantics using globular sets and
  discuss the issues which arise when using globular types instead.

% In \hott{}, a variant of \mltt{}, we reject proof-irrelevance so that the common interpretation of types as setoids has to be generalised. With the univalence axiom, we treat equivalence as equality and interpret types as \og{}. Inspired by Altenkirch's work \cite{txa:csl} and Brunerie's notes \cite{gb:wog}, we study and implement a syntactic definition of Grothendieck \wog{} in Agda which is a popular variant of \mltt{} and a famous theorem prover. It is the first step to model type theory with \wog{} so that we could eliminate the univalence axiom.

\end{abstract}

\category{F.4.1}{Mathematical Logic and Formal Languages}{Lambda calculus and related systems, Mechanical theorem proving}

\terms{Theory}

\keywords{Type Theory, Homotopy Type Theory, Category Theory, Formalisation, Higher dimensional structures, Agda}



\section{Introduction}

% Background

%why do we need to use omega groupoid

In Type Theory, a type can be interpreted as a setoid which is a set equipped with an equivalence relation \cite{alti:lics99}.
The equivalence proof of the relation consists of reflexivity, symmetry and transitivity whose proofs are unique. 
However in \hott{}, we reject the principle of uniqueness of identity proofs (UIP). 
Instead we accept the univalence axiom which says that equality of types is weakly equivalent to weak equivalence. 
Weak equivalence can be seen as a refinement of isomorphism without UIP \cite{txa:csl}. 
In the higher-categorical setting, weak equivalence can be thought of as arising from isomorphisms by systematically replacing equalities by higher cells.  
For example, a weak equivalence 
between two objects $A$ and $B$ in a 2-category is a morphism $f : A \rightarrow B$ which has a
corresponding inverse morphism $ g : B \rightarrow A$, but instead of the
equalities $f ∘ g = 1_B$ and $g ∘ f = 1_A$ we have 2-cell isomorphisms $f ∘ g ≅ 1_B$ and $g ∘ f ≅ 1_A$. In an $\omega$-category, these later isomorphisms are weak equivalences again. As all equivalences in this paper are weak equivalences in this sense, from now on we say just equivalence.


Voevodsky proposed the univalence axiom which basically says that
isomorphic types are equal. This can be viewed as a strong
extensionality axiom and it does imply functional extensionality.  %(a
A coq proof of this can be found in \cite{uafe}) However, adding
univalence as an axiom destroys canonicity, i.e.\ that every closed
term of type $\mathbb{N}$ is reducible to a numeral. In the special
case of extensionality and assuming a strong version of UIP the first
author and coauthors were able to eliminate this issue
\cite{alti:lics99,alti:ott-conf} using setoids. However, it is not
clear how to generalize this in the absence of UIP to univalence which
is incompatible with UIP. To solve the problem we should generalise
the notion of setoids, namely to enrich the structure of the identity
proofs.


The generalised notion is called {\wogs} and was proposed by
Grothendieck 1983 in a famous manuscript \emph{Pursuing Stacks} \cite{gro:ps}. Maltsiniotis continued his work and suggested a simplification of the original definition which can be found in \cite{mal:gwog}. Later Ara also presents a slight variation of the simplication of {\wog} in \cite{ara:wog}. Categorically speaking an $\omega$-groupoid is an $\omega$-category in which morphisms on all levels are equivalences. As we know that a set can be seen as a discrete
category, a setoid is a category where every morphism between
any two objects is unique. A groupoid is more generalised, every morphism is
an isomorphism but the proof of isomorphism is unique, namely the
composition of a morphism with its inverse is equal to the identity. Similarly, an
$n$-groupoid is an $n$-category in which morphisms on all levels are
equivalences. {\wogs} (also called $\infty$-groupoid) is an
infinite version of $n$-groupoid. To model Type Theory without UIP we
also allow the equalities to be non-strict, in other words, they are
propositional but not necessarily definitional equalities. Finally we should use {\wog} to interpret types and eliminate the univalence axiom.

There are several approaches to formalise {\wog} in Type Theory, for instance, Altenkirch and Ryp\'a\v{c}ek \cite{txa:csl}, and Brunerie's notes \cite{gb:wog}.

This paper builds on the syntactic approach of
\cite{txa:csl} but simplifies it greatly following Brunerie's proposal
\cite{gb:wog} by replacing the distinct constants for each of the
higher coherence cells by a single constant $\mathsf{coh}$. In more detail, we
specify when a globular set is a {\wogs} by first defining a type
theory called {\tig} to describe the internal language of Grothendieck
{\wog}, then interpret it with a globular set and a dependent
function to it. All coherence laws of {\wog} are derivable from the
syntax, we will present some basic ones, for example reflexivity. Everything
is formalised in Agda, a theorem prover based on intensional
{\mltt}. This is the first attempt to formalise this approach in a
dependently typed language like Agda or Coq. One
of the main contributions of this paper is to use heterogeneous
equality for terms to overcome difficult problems encountered
when using the usual homogeneous one. We present the formalisation but
omit some complicated and less important programs, namely the
proofs of some lemmas or definitions of some auxiliary functions. It
is still possible for the reader who is interested in the details to
check the code online \cite{lfmtp-github}.  
%\footnote{The source code is available on %\url{github.com/nzl-nott}.}.

\subsection*{Agda}\label{Agda}

Agda is a programming language and development environment based on
Martin-Löf Type Theory \cite{agdawiki:main}. Readers with background in
Type Theory (e.g.\ from reading the introductory chapters of
\cite{hott}) should find it easy to read the Agda code presented
in this paper. Some hints: $\Pi$-types are written in a generalized
arrow notation $(x : A) → B$ for $\Pi x:A.B$, implicit arguments are
indicated by curly brackets, e.g.\ $\{x : A\} → B$, in this case Agda
will try to generate the argument automatically and we do not supply it
to make the code more readable. If we do not want to supply $A$ because
it can be inferred we write $\forall x$ or $\forall\{x\}$.
Agda uses a flexible mixfix notation
where the positions of arguments are indicated by underscores.
E.g.\ $\_⇒\_$ is one identifier which can be applied to two arguments as
in $A ⇒ B$. Underscore can also be used as wildcards, if some arguments can be automatically inferred by Agda.
The keyword \textbf{data} is used to define constructor based datatypes (both
inductive and coinductive) and \textbf{record} to define dependent record
types (this generalizes $\Sigma$-types). The representation of
coinductive types and more generally mixed inductive/coinductive types
\cite{txa:mpc2010g}
uses the type constructor $\infty$ whose elements are computations of type
$A$ which are written as $\sharp ~a$ where $a$ is an expression which can be
evaluated to an element of type~$A$.

\section{Syntax of weak {\Large$\omega$}-groupoids}\label{sec:syntax}
%
We develop the type theory of $\omega$-groupoids formally, following
\cite{gb:wog}. This is a type theory with only one type former which
we can view as equality type and interpret as the homset of the
$\omega$-groupoid. There are no definitional equalities, this
corresponds to the fact that we consider \emph{weak} $\omega$-groupoids. None of the groupoid laws on any levels are strict (i.e.\ definitional) but all are witnessed by
terms. Compared to \cite{txa:csl} the definition is greatly
simplified by the observation that all laws of a weak $\omega$-groupoid follow from the existence of coherence constants for
any contractible context.

In our formalisation we exploit the more liberal way to do mutual
definitions in Agda, which was implemented recently following up a
suggestion by the first author. It allows us to first introduce a type
former but give its definition later.

Since we are avoiding definitional equalities we have to define a
syntactic substitution operation which we need for the general
statement of the coherence constants. However, defining these
constants requires us to prove a number of substitution laws which
with the usual definition of identity types take a very
complex mutually recursive form (see \cite{txa:csl}). We address this
issue by using heterogeneous equality \cite{mcbride:elimination}. Although 
it exploits UIP, our approach is sound because UIP holds for the
syntax. See Section \ref{sec:het} for a more details.



% Since the definitions of contexts, types and terms involve each others, we adopt a more liberal way to do mutual definition in Agda which is a feature available since version 2.2.10. Something declared is free to use even it has not been completely defined.


\subsection{Basic Objects}

We first declare the syntax of our type theory which is
called \tig{} namely the internal language of \wog. Since the definitions of syntactic objects involve each other, it is essential to define them in a inductive-inductive way. Agda allows us to state the types and constructors separately for involved inductive-inductive definitions. The following declarations in order are contexts as sets,
types are sets dependent on contexts, terms and variables are sets
dependent on types, context morphisms and contractible contexts.

\begin{code}
data Con           : Set
data Ty (Γ : Con)  : Set
data Tm            : {Γ : Con}(A : Ty Γ) → Set
data Var           : {Γ : Con}(A : Ty Γ) → Set
data _⇒_           : Con → Con → Set
data isContr       : Con → Set
\end{code}
Contexts are inductively defined as either an empty context or
a context with a type in it.

\begin{code}
data Con where
  ε     : Con
  _,_   : (Γ : Con)(A : Ty Γ) → Con
\end{code}
Types are defined as either $*$ which we
call 0-cells, or a equality type between two terms of some type $A$. If the
type $A$ is an $n$-cell then we call its equality type an $(n+1)$-cell.

\begin{code}
data Ty Γ where
  *     : Ty Γ
  _=h_  : {A : Ty Γ}(a b : Tm A) → Ty Γ
\end{code}

\subsection{Heterogeneous Equality for Terms}\label{sec:het}

One of the big challenges we encountered was the difficulty to
formalise and reason about the equalities of terms, which is
essential when defining substitution. When the usual homogeneous identity types
are used one has to use substitution to unify
the types on both sides of equality types. This results in
$\mathit{subst}$ to appear in terms, about which one has to state
substitution lemmas. This further pollutes syntax requiring lemmas
about lemmas, lemmas about lemmas about lemmas, etc. For example, we
have to prove that using $\mathit{subst}$ consecutively with two equalities
of types is propositionally equal to using $\mathit{subst}$ with the
composition of these two equalities. As the complexity of the proofs
grows more lemmas are needed. The resulting
recurrence pattern has been identified and implemented in
\cite{txa:csl} for the special cases of coherence cells for
associativity, units and interchange. However it is not clear how that
approach could be adapted to the present, much more economical
formulation of {\wog}. Moreover, the complexity brings the
Agda type checker to its limits and correctness into question.

The idea of heterogenous equality (or JM equality) due to McBride
\cite{mcbride:elimination} used to resolve this issue is to define
equality for terms of different types, but its inhabitants only for
terms of definitionally equal types. However, the corresponding
elimination principle relies on UIP.  In \itt, UIP is not provable
in general, namely not all types are h-sets (homotopy
0-types). However every type with decidable equality is an h-set.
Inductive types with finitary constructors have decidable equality. In
our case, the types which stand for syntactic objects (contexts,
types, terms) are all inductive-inductive types with finitary
constructors. It follows by Hedberg's Theorem \cite{hed:98} that any
type with decidable equality satisfies UIP and it therefore follows
that the syntax staisfies UIP. Because, the equality of syntactic
types is unique, it is safe to use heterogeneous equality and proceed
without using substitution lemmas which would otherwise be necessary
to match terms of different types. From a computational perspective,
it means that every equality of types can be reduced to
$\mathit{refl}$ and using $\mathit{subst}$ to construct terms is
proof-irrelevant, which is expressed in the following definition of
heterogeneous equality for terms.


\begin{code}
data _≅_ {Γ : Con}{A : Ty Γ} :
         {B : Ty Γ} → Tm A → Tm B → Set where
  refl : (b : Tm A) → b ≅ b
\end{code}
\AgdaHide{
\begin{code}

_-¹          : ∀{Γ : Con}{A B : Ty Γ}{a : Tm A}{b : Tm B} → a ≅ b → b ≅ a
(refl _) -¹  = refl _

infixr 4 _∾_ 

_∾_ : {Γ : Con}
      {A B C : Ty Γ}
      {a : Tm A}{b : Tm B}{c : Tm C} →
      a ≅ b → 
      b ≅ c 
    → a ≅ c
_∾_ {c = c} (refl .c) (refl .c) = refl c

\end{code}
}
Once we have heterogeneous equality for terms, we can define a proof-irrelevant substitution which we call coercion
since it gives us a term of type $A$ if we have a term of type $B$ and the
two types are equal. We can also prove that the coerced term is heterogeneously equal to the
original term. Combining these definitions, it is much
more convenient to formalise and reason about term equations.

\begin{code}
_⟦_⟫        : {Γ : Con}{A B : Ty Γ}(a : Tm B) 
            → A ≡ B → Tm A
a ⟦ refl ⟫  = a

cohOp       : {Γ : Con}{A B : Ty Γ}{a : Tm B}(p : A ≡ B) 
            → a ⟦ p ⟫ ≅ a
cohOp refl  = refl _
\end{code}

% could delete the explanation of this lemma

%It is sufficient to prove the original terms are equal if we coerced them using the same proof. This lemma is useful later.

\AgdaHide{
\begin{code}

cohOp-eq : {Γ : Con}{A B : Ty Γ}{a b : Tm B}{p : A ≡ B} → (a ≅ b) 
         → (a ⟦ p ⟫ ≅ b ⟦ p ⟫)
cohOp-eq {Γ} {.B} {B} {a} {b} {refl} r = r

cohOp-hom : {Γ : Con}{A B : Ty Γ}{a b : Tm B}(p : A ≡ B) → (a ⟦ p ⟫ =h b ⟦ p ⟫) ≡ (a =h b)
cohOp-hom refl = refl

cong≅ : {Γ Δ : Con}{A B : Ty Γ}{a : Tm A}{b : Tm B}{D : Ty Γ → Ty Δ} →
        (f : {C : Ty Γ} → Tm C → Tm (D C)) → 
        a ≅ b 
      → f a ≅ f b
cong≅ f (refl _) = refl _

\end{code}
}


\subsection{Substitutions}

In this paper we usually define a set of functions together and
we name a function $\mathsf{x}$ as $\mathsf{xC}$ for contexts, $\mathsf{xT}$ for types, $\mathsf{xV}$ for
variables $\mathsf{xtm}$ for terms and $\mathsf{xS}$ for context morphisms (substitutions). For example
the substitutions are declared as follows:

\begin{code}
_[_]T   : ∀{Γ Δ} → Ty Δ → Γ ⇒ Δ → Ty Γ
_[_]V   : ∀{Γ Δ A} → Var A → (δ : Γ ⇒ Δ) → Tm (A [ δ ]T)
_[_]tm  : ∀{Γ Δ A} → Tm A → (δ : Γ ⇒ Δ) → Tm (A [ δ ]T)    
\end{code}
Indeed, composition of context morphisms can be understood as substitution for context morphisms as well.

\begin{code}
_⊚_ : ∀{Γ Δ Θ} → Δ ⇒ Θ → (δ : Γ ⇒ Δ) → Γ ⇒ Θ   
\end{code}
Context morphisms are defined inductively similarly to contexts. A context morphism is a list of terms corresponding to the list of types in the context on the right hand side of the morphism.

\begin{code}
data _⇒_ where
  •    : ∀{Γ} → Γ ⇒ ε
  _,_  : ∀{Γ Δ}(δ : Γ ⇒ Δ){A : Ty Δ}(a : Tm (A [ δ ]T))
       → Γ ⇒ (Δ , A)
\end{code}

\subsection{Weakening}

We can freely add types to the contexts of any given type judgments,
term judgments or context morphisms. These are the weakening rules.

\begin{code}   
_+T_   : ∀{Γ}(A : Ty Γ)(B : Ty Γ) → Ty (Γ , B)
_+tm_  : ∀{Γ A}(a : Tm A)(B : Ty Γ) → Tm (A +T B)   
_+S_   : ∀{Γ Δ}(δ : Γ ⇒ Δ)(B : Ty Γ) → (Γ , B) ⇒ Δ   
\end{code}
%We could first define the weakening and substitution for types.
\AgdaHide{
\begin{code}

*        +T B = *
(a =h b) +T B = a +tm B =h b +tm B


*        [ δ ]T = * 
(a =h b) [ δ ]T = a [ δ ]tm =h b [ δ ]tm

\end{code}
}

\subsection{Terms}

A term can be either a variable or a coherence constant ($\AgdaInductiveConstructor{coh}$).

We first define variables separately using the weakening rules. We
use typed de Bruijn indices to define variables as either the rightmost
variable of the context, or some variable in the context which can be
found by cancelling the rightmost variable along with each $\AgdaInductiveConstructor{vS}$.

\begin{code}
data Var where
  v0 : ∀{Γ}{A : Ty Γ}              → Var (A +T A)
  vS : ∀{Γ}{A B : Ty Γ}(x : Var A) → Var (A +T B)
\end{code}
The coherence constants are one of the major part of this syntax, which
are primitive terms of the primitive types in contractible contexts
which will be introduced later. Indeed it encodes the fact that any type in a contractible context is inhabited, and so are the types generated by substituting into a contractible context.

\begin{code}
data Tm where
  var  : ∀{Γ}{A : Ty Γ} → Var A → Tm A
  coh  : ∀{Γ Δ} → isContr Δ → (δ : Γ ⇒ Δ) 
       → (A : Ty Δ) → Tm (A [ δ ]T)
\end{code}
\AgdaHide{
\begin{code}
cohOpV : {Γ : Con}{A B : Ty Γ}{x : Var A}(p : A ≡ B) → var (subst Var p x) ≅ var x
cohOpV {x = x} refl = refl (var x)

cohOpVs : {Γ : Con}{A B C : Ty Γ}{x : Var A}(p : A ≡ B) → var (vS {B = C} (subst Var p x)) ≅ var (vS x)
cohOpVs {x = x} refl = refl (var (vS x))

coh-eq : {Γ Δ : Con}{isc : isContr Δ}{γ δ : Γ ⇒ Δ}{A : Ty Δ} → γ ≡ δ → coh isc γ A ≅ coh isc δ A 
coh-eq refl = refl _

\end{code}
}

\subsection{Contractible contexts}
With variables defined, it is possible to formalise another core part of the syntactic framework, \emph{contractible
contexts}. Intuitively speaking, a context is contractible if its geometric
realization is contractible to a point. It either contains one
variable of the type $*$ which is the base case, or we can extend a contractible context with a
variable of an existing type and an $n$-cell, namely a morphism,
between the new variable and some existing variable. Contractibility
of contexts is defined as follows:

\begin{code}
data isContr where
  c*   : isContr (ε , *)
  ext  : ∀{Γ} → isContr Γ → {A : Ty Γ}(x : Var A) 
       → isContr (Γ , A , (var (vS x) =h var v0))     
\end{code}

\AgdaHide{
\begin{code}

hom≡ : {Γ : Con}{A A' : Ty Γ}
                {a : Tm A}{a' : Tm A'}(q : a ≅ a')
                {b : Tm A}{b' : Tm A'}(r : b ≅ b')
                → (a =h b) ≡ (a' =h b')
hom≡ {Γ} {.A'} {A'} {.a'} {a'} (refl .a') {.b'} {b'} (refl .b') = refl


S-eq : {Γ Δ : Con}{γ δ : Γ ⇒ Δ}{A : Ty Δ}
        {a : Tm (A [ γ ]T)}{a' : Tm (A [ δ ]T)} 
        → γ ≡ δ → a ≅ a' 
        → _≡_ {_} {Γ ⇒ (Δ , A)} (γ , a) (δ , a')
S-eq refl (refl _) = refl

\end{code}
}


\subsection{Lemmas}

Since contexts, types, variables and
terms are all mutually defined, most of their properties have to
be proved simultaneously. Note that we are free to define all the
types first and all the definitions (not shown) later. 

The following lemmas are essential for the constructions and theorem
proving later.  The first set of lemmas states that to substitute a
type, a variable, a term, or a context morphism with two context
morphisms consecutively, is equivalent to substitute with the
composition of the two context morphisms:

\begin{code}
[⊚]T    : ∀{Γ Δ Θ A}{θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ} 
        → A [ θ ⊚ δ ]T ≡ (A [ θ ]T)[ δ ]T  

[⊚]v    : ∀{Γ Δ Θ A}(x : Var A){θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}
        → x [ θ ⊚ δ ]V ≅ (x [ θ ]V) [ δ ]tm

[⊚]tm   : ∀{Γ Δ Θ A}(a : Tm A){θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}
        → a [ θ ⊚ δ ]tm ≅ (a [ θ ]tm) [ δ ]tm

⊚assoc  : ∀{Γ Δ Θ Ω}(γ : Θ ⇒ Ω){θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}  
        → (γ ⊚ θ) ⊚ δ ≡ γ ⊚ (θ ⊚ δ)  
\end{code}
\AgdaHide{
\begin{code}

•       ⊚ δ = •
(δ , a) ⊚ δ' = (δ ⊚ δ') , a [ δ' ]tm ⟦ [⊚]T ⟫

\end{code}
}
The second set states that weakening inside substitution is equivalent to weakening outside:

\begin{code}
[+S]T   : ∀{Γ Δ A B}{δ : Γ ⇒ Δ}
        → A [ δ +S B ]T ≡ (A [ δ ]T) +T B 

[+S]tm  : ∀{Γ Δ A B}(a : Tm A){δ : Γ ⇒ Δ}
        → a [ δ +S B ]tm ≅ (a [ δ ]tm) +tm B

[+S]S   : ∀{Γ Δ Θ B}{δ : Δ ⇒ Θ}{γ : Γ ⇒ Δ}
        → δ ⊚ (γ +S B) ≡ (δ ⊚ γ) +S B
\end{code}
%There are also some auxiliary functions derived from these lemmas. For instance, the function shown below is used a lot in proofs.
\AgdaHide{
\begin{code}
wk-tm+      : {Γ Δ : Con}{A : Ty Δ}{δ : Γ ⇒ Δ}(B : Ty Γ) 
            → Tm (A [ δ ]T +T B) → Tm (A [ δ +S B ]T)
wk-tm+ B t  = t ⟦ [+S]T ⟫
\end{code}
}
\AgdaHide{
\begin{code}
•       +S B = •
(δ , a) +S B = (δ +S B) , wk-tm+ B (a +tm B)

[+S]T {A = *}     = refl
[+S]T {A = a =h b} = hom≡ ([+S]tm a) ([+S]tm b)
\end{code}
}
We can cancel the last term in the substitution for weakened objects
since weakening doesn't introduce new variables in types and terms.

\begin{code}
+T[,]T    : ∀{Γ Δ A B}{δ : Γ ⇒ Δ}{b : Tm (B [ δ ]T)} 
          → (A +T B) [ δ , b ]T ≡ A [ δ ]T

+tm[,]tm  : ∀{Γ Δ A B}{δ : Γ ⇒ Δ}{c : Tm (B [ δ ]T)}
          → (a : Tm A) 
          → (a +tm B) [ δ , c ]tm ≅ a [ δ ]tm 
\end{code}
\AgdaHide{
\begin{code}

(var x)     +tm B = var (vS x)
(coh cΔ δ A) +tm B = coh cΔ (δ +S B) A ⟦ sym [+S]T ⟫ 

cong+tm : {Γ : Con}{A B C : Ty Γ}{a : Tm A}{b : Tm B} → 
          a ≅ b
        → a +tm C ≅ b +tm C
cong+tm (refl _) = refl _

cong+tm2 : {Γ : Con}{A B C : Ty Γ}
           {a : Tm B}(p : A ≡ B) 
         → a +tm C ≅ a ⟦ p ⟫ +tm C
cong+tm2 refl = refl _

wk-T : {Δ : Con}
       {A B C : Ty Δ}
       → A ≡ B → A +T C ≡ B +T C
wk-T refl = refl

wk-tm : {Γ Δ : Con}
         {A : Ty Δ}{δ : Γ ⇒ Δ}
         {B : Ty Δ}{b : Tm (B [ δ ]T)}  
         → Tm (A [ δ ]T) → Tm ((A +T B) [ δ , b ]T)
wk-tm t = t ⟦ +T[,]T ⟫

v0   [ δ , a ]V = wk-tm a
vS x [ δ , a ]V = wk-tm (x [ δ ]V)


wk-coh : {Γ Δ : Con}
         {A : Ty Δ}{δ : Γ ⇒ Δ}
         {B : Ty Δ}{b : Tm (B [ δ ]T)}  
         {t : Tm (A [ δ ]T)} 
         → wk-tm {B = B} {b = b} t ≅ t
wk-coh = cohOp +T[,]T

wk-coh+ : {Γ Δ : Con}
         {A : Ty Δ}{δ : Γ ⇒ Δ}
         {B : Ty Γ} 
         {x : Tm (A [ δ ]T +T B)}
          → wk-tm+ B x ≅ x
wk-coh+ = cohOp [+S]T

wk-hom : {Γ Δ : Con}
         {A : Ty Δ}{δ : Γ ⇒ Δ}
         {B : Ty Δ}{b : Tm (B [ δ ]T)}  
         {x y : Tm (A [ δ ]T)}
         → (wk-tm {B = B} {b = b} x =h wk-tm {B = B} {b = b} y) ≡ (x =h y)
wk-hom = hom≡ wk-coh wk-coh


wk-hom+ : {Γ Δ : Con}
         {A : Ty Δ}{δ : Γ ⇒ Δ}
         {B : Ty Γ} 
         {x y : Tm (A [ δ ]T +T B)}
         → (wk-tm+ B x =h wk-tm+ B y) ≡ (x =h y)
wk-hom+ = hom≡ wk-coh+ wk-coh+


wk-⊚ : {Γ Δ Θ : Con}
       {θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}{A : Ty Θ}
       → Tm ((A [ θ ]T)[ δ ]T) → Tm (A [ θ ⊚ δ ]T)
wk-⊚ t = t ⟦ [⊚]T ⟫

[+S]S {δ = •} = refl
[+S]S {δ = δ , a} = S-eq [+S]S (cohOp [⊚]T ∾ ([+S]tm a ∾ cong+tm2 [⊚]T) ∾ wk-coh+ -¹)


wk+S+T : ∀{Γ Δ : Con}{A : Ty Γ}{B : Ty Δ}
          {γ}{C} → 
          A [ γ ]T ≡ C 
       → A [ γ +S B ]T ≡ C +T B
wk+S+T eq = trans [+S]T (wk-T eq)

wk+S+tm : {Γ Δ : Con}{A : Ty Γ}{B : Ty Δ}
          (a : Tm A){C : Ty Δ}{γ : Δ ⇒ Γ}{c : Tm C} →
          a [ γ ]tm ≅ c 
        → a [ γ +S B ]tm ≅ c +tm B
wk+S+tm _ eq = [+S]tm _ ∾ cong+tm eq


wk+S+S : ∀{Γ Δ Δ₁ : Con}{δ : Δ ⇒ Δ₁}{γ : Γ ⇒ Δ}{ω : Γ ⇒ Δ₁}{B : Ty Γ}
       → δ ⊚ γ ≡ ω
       → δ ⊚ (γ +S B) ≡ ω +S B
wk+S+S eq = trans [+S]S (cong (λ x → x +S _) eq)


[⊚]T {A = *} = refl
[⊚]T {A = _=h_ {A} a b} = hom≡ ([⊚]tm _) ([⊚]tm _) 

+T[,]T {A = *} = refl
+T[,]T {A = _=h_ {A} a b} = hom≡  (+tm[,]tm _) (+tm[,]tm _)

\end{code}
}
Most of the substitutions are defined as usual, except the one for coherence constants. In this case, we substitute in the context morphism part and one of the lemmas declared above is used.

\begin{code}
var x       [ δ ]tm = x [ δ ]V
coh cΔ γ A  [ δ ]tm = coh cΔ (γ ⊚ δ) A ⟦ sym [⊚]T ⟫
\end{code}


\AgdaHide{
\begin{code}

-- congruence

congT : ∀ {Γ Δ : Con}{A B : Ty Δ}{γ : Γ ⇒ Δ} → A ≡ B → A [ γ ]T ≡ B [ γ ]T 
congT refl = refl


congT2 : ∀ {Γ Δ} → {δ γ : Δ ⇒ Γ}{A : Ty Γ} → δ ≡ γ → A [ δ ]T ≡ A [ γ ]T
congT2 refl = refl 

congV : {Γ Δ : Con}{A B : Ty Δ}{a : Var A}{b : Var B} →
     var a ≅ var b → 
     {δ : Γ ⇒ Δ} 
     → a [ δ ]V ≅ b [ δ ]V
congV {Γ} {Δ} {.B} {B} {.b} {b} (refl .(var b)) = refl _

congtm : {Γ Δ : Con}{A B : Ty Γ}{a : Tm A}{b : Tm B}
      (p : a ≅ b) → 
      {δ : Δ ⇒ Γ}
      → a [ δ ]tm ≅ b [ δ ]tm
congtm (refl _) = refl _ 

congtm2 : {Γ Δ : Con}{A : Ty Γ}{a : Tm A}
          {δ γ : Δ ⇒ Γ} →
          (p : δ ≡ γ)
        → a [ δ ]tm ≅ a [ γ ]tm
congtm2 refl = refl _

⊚assoc • = refl
⊚assoc (_,_ γ {A} a) = S-eq (⊚assoc γ) 
    (cohOp [⊚]T 
    ∾ (congtm (cohOp [⊚]T)
    ∾ ((cohOp [⊚]T 
    ∾ [⊚]tm a) -¹)))


[⊚]v (v0 {Γ₁} {A}) {θ , a}  = wk-coh ∾ cohOp [⊚]T ∾ congtm (cohOp +T[,]T -¹) 
[⊚]v (vS {Γ₁} {A} {B} x) {θ , a} = 
  wk-coh ∾ ([⊚]v x ∾ (congtm (cohOp +T[,]T) -¹))



[⊚]tm (var x) = [⊚]v x
[⊚]tm (coh c γ A) = cohOp (sym [⊚]T) ∾ (coh-eq (sym (⊚assoc γ)) ∾ cohOp (sym [⊚]T) -¹) ∾ congtm (cohOp (sym [⊚]T) -¹)


⊚wk : ∀{Γ Δ Δ₁}{B : Ty Δ}(γ : Δ ⇒ Δ₁){δ : Γ ⇒ Δ}{c : Tm (B [ δ ]T)} → (γ +S B) ⊚ (δ , c) ≡ γ ⊚ δ
⊚wk • = refl
⊚wk (_,_ γ {A} a) = S-eq (⊚wk γ) (cohOp [⊚]T ∾ (congtm (cohOp [+S]T) ∾ +tm[,]tm a) ∾ cohOp [⊚]T -¹)

+tm[,]tm (var x) = cohOp +T[,]T
+tm[,]tm (coh x γ A) = congtm (cohOp (sym [+S]T)) ∾ cohOp (sym [⊚]T) ∾ coh-eq (⊚wk γ) ∾ cohOp (sym [⊚]T) -¹



[+S]V : {Γ Δ : Con}{A : Ty Δ}
         (x : Var A){δ : Γ ⇒ Δ}
         {B : Ty Γ}
         → x [ δ +S B ]V ≅ (x [ δ ]V) +tm B
[+S]V v0 {_,_ δ {A} a} = wk-coh ∾ wk-coh+ ∾ cong+tm2 +T[,]T
[+S]V (vS x) {δ , a} = wk-coh ∾ [+S]V x ∾ cong+tm2 +T[,]T


[+S]tm (var x) = [+S]V x
[+S]tm (coh x δ A) = cohOp (sym [⊚]T) ∾ coh-eq [+S]S ∾ cohOp (sym [+S]T) -¹ ∾ cong+tm2 (sym [⊚]T)


-- some widely-used contexts

x:* : Con
x:* = ε , *

x:*,y:*,α:x=y : Con
x:*,y:*,α:x=y = x:* , * , (var (vS v0) =h var v0)

vX : Tm {x:*,y:*,α:x=y} *
vX = var (vS (vS v0))

vY : Tm {x:*,y:*,α:x=y} *
vY = var (vS v0)

vα : Tm {x:*,y:*,α:x=y} (vX =h vY)
vα = var v0

x:*,y:*,α:x=y,z:*,β:y=z : Con
x:*,y:*,α:x=y,z:*,β:y=z = x:*,y:*,α:x=y , * , (var (vS (vS v0)) =h var v0)

vZ : Tm {x:*,y:*,α:x=y,z:*,β:y=z} *
vZ = var (vS v0)

vβ : Tm {x:*,y:*,α:x=y,z:*,β:y=z} (vY +tm _ +tm _ =h vZ)
vβ = var v0

\end{code}
}

\section{Some Important Derivable Constructions}

\input{IdentityContextMorphisms}

\input{Suspension}

\input{GroupoidStructure}

\input{Telescopes2}
\vspace*{2\baselineskip}
\section{Semantics}

\subsection{Globular Types}

\input{GlobularTypes}

%\txa{Can we show that substitution is correct}
%\txa{Some discussion on why we do not need coherence laws.}

\input{Semantics}



\section{Conclusion}

In this paper, we presented an implementation of \wog{} following Brunerie's suggestion. Briefly speaking, we defined the syntax of the type theory \tig, then a weak $\omega$-groupoid is a globular set with the interpretation of the syntax. To overcome some technical problems, we used heterogeneous equality for terms, some auxiliary functions and loop context in all implementation. We constructed the identity morphisms and verified some groupoid laws in the syntactic framework. The suspensions for all sorts of objects were also defined for other later constructions.

There is still a lot of work to do within the syntactic framework. For instance, we would like to investigate the relation between the \tig{} and a type theory with equality types and $J$ eliminator which is called $\mathcal{T}_{eq}$. One direction is to simulate the $J$ eliminator syntactically in \tig{} as we mentioned before, the other direction is to derive J using $coh$ if we can prove that the $\mathcal{T}_{eq}$ is a weak $\omega$-groupoid. The syntax could be simplified by adopting categories with families. An alternative may be to use higher inductive types directly to formalize the syntax of type theory. 

We would like to formalise a proof of that $\AgdaFunction{Idω}$ is a weak $\omega$-groupoid, but the base set in a globular set is an h-set which is incompatible with $\AgdaFunction{Idω}$. Perhaps we could solve the problem by instead proving a syntactic result, namely that the theory we have presented here and the theory of equality types with $J$ eliminator are equivalent. Finally, to model the type theory with \wog and to eliminate the univalence axiom would be the most challenging task in the future. 

\section{Acknowledgements}

The first and second author would like to thank the organizers and
other participants of the special year on homotopy type theory at the
Institute for Advanced Study where they had many interesting
discussion topics related to the work presented in this
paper. Especially we all would like to acknowledge Guillaume
Brunerie's proposal which made this work possible. The second author would like to thank Ambrus Kaposi, Fredrik Nordvall Forsberg and Nicolai Kraus for helpful discussions.

\bibliography{latex/my.bib}

\end{document}
