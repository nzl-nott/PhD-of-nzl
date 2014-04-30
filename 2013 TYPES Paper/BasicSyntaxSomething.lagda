\documentclass[a4paper,UKenglish]{lipics}

\PassOptionsToPackage{utf8x}{inputenc}

\bibliographystyle{plain}

%agda literal file
\usepackage{agda}

\usepackage{dsfont}
\usepackage{amsthm}
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

\newcommand{\wig}{weak $\infty$-groupoids}
\newcommand{\og}{$\omega$-groupoids}
\newcommand{\wog}{weak $\omega$-groupoids}
\newcommand{\hott}{Homotopy Type Theory}
\newcommand{\ott}{Observational Type Theory}
\newcommand{\tig}{$\mathcal{T}_{\infty-groupoid}$}


\newcommand{\new}{\textcolor{red}}

\begin{document}
\pagenumbering{gobble}
%\title{An Implementation of Syntactic Weak $\omega$-Groupoids in Agda}
\title{Some constructions on $\omega$-groupoids}

\subjclass{F.4.1 Lambda calculus and related systems, F.4.1 Mechanical theorem proving}

\keywords{Type Theory, Homotopy Type Theory, Category Theory, Higher dimensional structures}

\author[1]{Thorsten Altenkirch}
\author[1]{Nuo Li}
\author[2]{Ond\v{r}ej Ryp\'a\v{c}ek}
\affil[1]{University of Nottingham}
\affil[2]{University of Oxford}
\authorrunning{T.Altenkirch, N.Li and O.Ryp\'a\v{c}ek}

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
  semantics of Homotopy Type Theory \cite{hott}.  Following up on our previous formalisation \cite{txa:csl}
  and Brunerie's notes \cite{gb:wog}, we present a new formalisation of the syntax
  of weak $\omega$-groupoids in Agda using heterogeneous equality. We show how 
  to recover basic constructions on $\omega$-groupoids using suspension and replacement. In particular we show that any type forms 
  a groupoid and that we can derive higher dimensional composition. We present a possible semantics using globular sets and discuss
  the issues which arise when using globular types instead.

% In \hott{}, a variant of \mltt{}, we reject proof-irrelevance so that the common interpretation of types as setoids has to be generalised. With the univalence axiom, we treat equivalence as equality and interpret types as \og{}. Inspired by Altenkirch's work \cite{txa:csl} and Brunerie's notes \cite{gb:wog}, we study and implement a syntactic definition of Grothendieck \wog{} in Agda which is a popular variant of \mltt{} and a famous theorem prover. It is the first step to model type theory with \wog{} so that we could eliminate the univalence axiom.

\end{abstract}



\section{Introduction}

% Background

%why do we need to use omega groupoid

In Type Theory, a type can be interpreted as a setoid which is a set equipped with an equivalence relation \cite{alti:lics99}. The equivalence proof of the relation consists of reflexivity, symmetry and transitivity whose proofs are unique. However in \hott{}, we reject the principle of uniqueness of identity proofs (UIP). Instead we accept the univalence axiom which says that equality of types is weakly equivalent to weak equivalence. Weak equivalence can be seen as a refinement of isomorphism without UIP \cite{txa:csl}. For example, a weak equivalence
between two objects A and B in a 2-category is a morphism $f : A \to B$ which has a
corresponding inverse morphism $ g : B \to A$, but instead of the
proofs of isomorphism $f ∘ g = 1_B$ and  $g ∘ f = 1_A$ we have two
2-cell isomorphisms  $f ∘ g ≅ 1_B$ and  $g ∘ f ≅ 1_A$. 

Voevodsky proposed the univalence axiom which basically says that
isomorphic types are equal. This can be viewed as a strong
extensionality axiom and it does imply functional extensionality (a
coq proof of this can be found in \cite{uafe}). However, adding
univalence as an axiom destroys canonicity, i.e. that every closed
term of type $\mathbb{N}$ is reducible to a numeral. In the special case of
extensionality and assuming a strong version of UIP we were able to
eliminate this issue \cite{alti:lics99,alti:ott-conf} using
setoids. However, it is not clear how to generalize this in the
absence of UIP to
univalence which is incompatible with UIP.  To solve the problem we
should generalise the notion of setoids, namely to enrich the
structure of the identity proofs.


The generalised notion is called {\wog} and was proposed by
Grothendieck 1983 in a famous manuscript \emph{Pursuing Stacks} \cite{gro:ps}. Maltsiniotis continued his work and suggested a simplification of the original definition which can be found in \cite{mal:gwog}. Later Ara also presents a slight variation of the simplication of {\wog} in \cite{ara:wog}. Categorically speaking an $\omega$-groupoid is an $\omega$-category in which morphisms on all levels are equivalences. As we know that a set can be seen as a discrete
category, a setoid is a category where every morphism is unique between
two objects. A groupoid is more generalised, every morphism is
isomorphism but the proof of isomorphism is unique, namely the composition of a morphism with its inverse is equal to an identity morphism. Similarly, an
n-groupoid is an n-category in which morphisms on all levels are
equivalence. {\og} which are also called $\infty$-groupoids is an
infinite version of n-groupoids. To model Type Theory without UIP we
also require the equalities to be non-strict, in other words, they are
not definitionally equalities. Finally we should use {\wog} to interpret types and eliminate the univalence axiom.

There are several approaches to formalise {\wog} in Type Theory. For instance, Altenkirch and Ryp\'a\v{c}ek \cite{txa:csl}, and Brunerie's notes \cite{gb:wog}.
This paper mainly explains an implementation of {\wog} following Brunerie's approach in Agda which is a well-known theorem prover and also a variant of intensional {\mltt}. \new{This is the first attempt to formalise this approach in Agda, and other languages like Coq.} The approach is to specify when a globular set is a {\wog} by first defining a type theory called {\tig} to describe the internal language
of Grothendieck {\wog}, then interpret it with a globular set and a dependent function. All coherence laws of the {\wog} should be derivable from the syntax, we will present some basic ones, for example reflexivity. One of the main contributions of this paper is to use the heterogeneous equality for terms to overcome some very difficult problems when we used the normal homogeneous one. In this paper, we omit some complicated and less important programs, namely the proofs of some lemmas or the definitions of some auxiliary functions. It is still possible for the reader who is interested in the details to check the code online, in which there are only some minor differences.

\section*{Acknowledgements}

The first and second author would like to thank the organizers and
other participants of the special year on homotopy type theory at the
Institute for Advanced Study where they had many interesting
discussion topics related to the work presented in this
paper. Especially we all would like to acknowledge Guillaume
Brunerie's proposal which made this work possible. 

\section{Syntax}\label{sec:syntax}

We develop the type theory of $\omega$-groupoids formally, following
\cite{gb:wog}. This is a Type Theory with only one type former which
we can view as equality types and interpret as the homsets of the
$\omega$-groupoid. There are no definitional equalities which
correspond to the fact that we consider weak $\omega$-groupoids. None of the groupoid laws on any levels are strict (i.e. definitional) but all are witnessed by
terms. Compared to \cite{txa:csl} the definition is very much
simplified by the observation that all laws of a weak $\omega$-groupoid follow from the existence of coherence constants for
any contractible context.

In our formalisation we exploit the more liberal way to do mutual
definitions in Agda, which was implemented recently following up a
suggestion by the first author. It allows us to first introduce a type
former but give its definition later.

Since we are avoiding definitional equalities we have to define a
syntactic substitution operation which we need for the general
statement of the coherence constants. However, defining this constant
requires us to prove a number of substitution laws at the same
time. We address this issue by using a heterogeneous equality which
exploits uniqueness of identity proofs (UIP). Note that UIP holds because all components defined here
are sets in the sense of Homotopy Type Theory.

% Since the definitions of contexts, types and terms involve each others, we adopt a more liberal way to do mutual definition in Agda which is a feature available since version 2.2.10. Something declared is free to use even it has not been completely defined.


\subsection{Basic Objects}

We first declare the syntax of our type theory which is
called \tig{} namely the internal language of \wog. The following declarations in order are contexts as sets,
types are sets dependent on contexts, terms and variables are sets
dependent on types, Contexts morphisms and the contractible contexts.

\begin{code}

data Con           : Set
data Ty (Γ : Con)  : Set
data Tm            : {Γ : Con}(A : Ty Γ) → Set
data Var           : {Γ : Con}(A : Ty Γ) → Set
data _⇒_           : Con → Con → Set
data isContr       : Con → Set
\end{code}

% Altenkirch also suggests to use Higher Inductive-Inductive definitions for these sets which he coined as Quotient Inductive-Inductive Types (QIIT), in other words, to given an equivalence relation for each of them as one constructor. However we do not use it here.

It is possible to complete the definition of contexts and types first. Contexts are inductively defined as either an empty context or a context with a type of it. Types are defined as either $*$ which we call it 0-cell, or a morphism between two terms of
some type A. If the type A is n-cell then we call the morphism $(n+1)$-cell. 

\begin{code}
data Con where
  ε     : Con
  _,_   : (Γ : Con)(A : Ty Γ) → Con


data Ty Γ where
  *     : Ty Γ
  _=h_  : {A : Ty Γ}(a b : Tm A) → Ty Γ
\end{code}

\subsection{Heterogeneous Equality for Terms}





\AgdaHide{
\begin{code}

{-


tyeq : ∀{Γ : Con}{A : Ty Γ}{a b a₁ b₁ : Tm A} → ((a =h b) ≡ (a₁ =h b₁)) → (a ≡ a₁) × (b ≡ b₁)
tyeq refl = refl ,, refl

tyeq2 : ∀{Γ : Con}{A A₁ : Ty Γ}{a b : Tm A}{a₁ b₁ : Tm A₁} → ((a =h b) ≡ (a₁ =h b₁)) → A ≡ A₁
tyeq2 refl = refl

open import Relation.Nullary

_≟ty_ : ∀{Γ : Con}(A B : Ty Γ) → Dec (A ≡ B)


_≟tm_ : ∀{Γ : Con}{A : Ty Γ}(a b : Tm A) → Dec (a ≡ b)


_≟ty_ * * = yes refl
_≟ty_ * (a =h b) = no (λ())
_≟ty_ (a =h b) * = no (λ())
_≟ty_ (_=h_ {A} a b) (_=h_ {A₁} a₁ b₁) with A ≟ty A₁ 
(a =h b) ≟ty (a₁ =h b₁) | yes refl with a ≟tm a₁ | b ≟tm b₁ 
(a =h b) ≟ty (.a =h .b) | yes refl | yes refl | yes refl = yes refl
(a =h b) ≟ty (.a =h b₁) | yes refl | yes refl | no ¬p = no (λ x → ¬p (proj₂ (tyeq x)))
(a =h b) ≟ty (a₁ =h b₁) | yes refl | no ¬p | q = no (λ x → ¬p (proj₁ (tyeq x)))
(a =h b) ≟ty (a₁ =h b₁) | no ¬p = no (λ x → ¬p (tyeq2 x))

-}


{-
data Var'           : {Γ : Con}(Last : Ty Γ)(Typ : Ty Γ) → Set


data Var' where
  v0 : {Γ : Con}{A : Ty Γ}              → Var' {Γ} A A
  vS : {Γ : Con}{A B : Ty Γ} → (x : Var' {Γ} B A) → {C : Ty (Γ , B)} 
                             → Var' {Γ , B} C (A +T B)


_≟v'_ : ∀(Γ : Con)(A B : Ty Γ)(a b : Var' A B) → Dec (a ≡ b)
_≟v'_ Γ A .A v0 v0 = yes refl
_≟v'_ .(Γ , B) .(A +T B) .(A +T B) v0 (vS {Γ} {A} {B} b) = no (λ ())
_≟v'_ .(Γ , B) .(A +T B) .(A +T B) (vS {Γ} {A} {B} a) v0 = ? -- no (λ ())
-- _≟v'_ .(Γ , B) A₁ .(A +T B) (vS {Γ} {A} {B} a) b = {!b!}
_≟v'_ Γ A B a b = {!b!}
-}

\end{code}
}






One of the big challenge we encountered at first is the difficulty to formalise and to reason about the equalities of terms, which is essential when defining substitution.
When we used the common identity types which are homogeneous, we had to use $subst$ function in Agda to unify the types on both sides of the equation. It created a lot of technical issues that made the encoding too involved to proceed. \new{A Case of complexity: For example, assume we have a context $\Gamma$, three types $A B : Ty \Gamma$ and we know $p : A \equiv B$. If we have a term $a : Tm  ~ A$ and a term $b : Tm  ~ B$, it is impossible to just write $a \equiv B$ because of type unification. We need to write $subst Tm p a \equiv b$. Again assume we have another type $C : Ty \Gamma$, $q : B \equiv C$ and a term of $c : Tm  ~ C$, to prove a possible lemma $a = c$, we have to write something like $subst  ~ Tm  ~ q ~ (subst~Tm  ~ p  ~ a)  ~ \equiv c$. Of course because of this we need to prove a coherence lemma $subst  ~ Tm  ~ q  ~ (subst  ~ Tm  ~ p  ~ a) \equiv subst  ~ Tm  ~ (trans  ~ p  ~ q) a$ and indeed, there are more lemmas to prove which simplfy the $subst$ issues.} However we found that the equality of syntactic types of given context which will be introduced later, is decidable which means that it is an h-set. In other words, the equality of syntactic types is unique, so that it is safe to use the JM equality (heterogeneous equality) for terms of different types. The heterogeneous equality for terms is inhabited only when their syntactic types are definitionally equal.

\new{In intensional type theory, the uniqueness of identity proof (UIP) in general is not provable, namely not all types are h-sets (homotopy 0-type). However it is justified to claim some types are h-sets. From the Hedberg Theorem we know that inductive types with finitary constructors is a set. Here these types which stands for syntactic components areinductive-inductive types with finitary constructors, and from the same reason, it is safe to claim the UIP for the syntacic contexts, types, terms and variables are all sets. Here we only the UIP for syntactic types so that we can adopt heterogeneous equality for terms which can simplify the work a lot if it is safe. The motivation of using the heterogeneous equality is due to the complexivity when manipulating equality of terms. Without the heterogeneous equality, most propositional equality of terms involves a lot of \emph{subst} (which substite certain values in the dependent type of terms), and repetative utilization of the coherence laws for \emph{subst}.
}

%Here we use it for the syntacic terms because it is dependent on types whose equality are decidable. It means that every equalit%y term can be normalised to refl. . Here we will give a formalised proof of the reason:
%

\begin{code}
data _≅_ {Γ : Con}{A : Ty Γ} : {B : Ty Γ} → Tm A → Tm B → Set where
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

Once we have the heterogeneous equality for terms, we can define a proof-irrelevant substitution which we call coercion here
since it gives us a term of type A if we have a term of type B and the
two types are equal. We can also prove that the coerced term is heterogeneously equal to the
original term. Combining these definitions, it is much
more convenient to formalise and to reason about term equations.

\begin{code}
_⟦_⟫        : {Γ : Con}{A B : Ty Γ}(a : Tm B) → A ≡ B → Tm A
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

With context morphism, we can define substitutions for types variables and terms. Indeed the
composition of contexts can be understood as substitution for context morphisms as well.

\begin{code}
_[_]T   : {Γ Δ : Con}            → Ty Δ    → (δ : Γ ⇒ Δ)   → Ty Γ        
_[_]V   : {Γ Δ : Con}{A : Ty Δ}  → Var A   → (δ : Γ ⇒ Δ)   → Tm (A [ δ ]T)
_[_]tm  : {Γ Δ : Con}{A : Ty Δ}  → Tm A    → (δ : Γ ⇒ Δ)   → Tm (A [ δ ]T)    
_⊚_     : {Γ Δ Θ : Con}          → Δ ⇒ Θ → (δ : Γ ⇒ Δ)   → Γ ⇒ Θ   
\end{code}


\subsection{Weakening Rules}

We can freely add types to the contexts of any given type
judgments, term judgments or context morphisms. These are weakening rules.

\begin{code}   
_+T_   : {Γ : Con}            (A : Ty Γ)   → (B : Ty Γ) → Ty (Γ , B)   
_+tm_  : {Γ : Con}{A : Ty Γ}  (a : Tm A)   → (B : Ty Γ) → Tm (A +T B)   
_+S_   : {Γ : Con}{Δ : Con}   (δ : Γ ⇒ Δ)  → (B : Ty Γ) → (Γ , B) ⇒ Δ   
\end{code}

%We could first define the weakening rule and substitution for types.

\AgdaHide{
\begin{code}

*        +T B = *
(a =h b) +T B = a +tm B =h b +tm B


*        [ δ ]T = * 
(a =h b) [ δ ]T = a [ δ ]tm =h b [ δ ]tm

\end{code}
}

To define the variables we have to use the weakening rules. We
use typed de Bruijn indices to define variables as either the rightmost
variable of the context, or some variable in the context which can be
found by cancelling the rightmost variable along with each $\mathsf{vS}$. The
coherence constants are one of the major part of this syntax, which
are primitive terms of the primitive types in contractible contexts
which will be introduced later. Since contexts, types, variables and
terms are all mutually defined, most of their properties have to
be proved simultaneously.


\begin{code}
data Var where
  v0 : {Γ : Con}{A : Ty Γ}              → Var (A +T A)
  vS : {Γ : Con}{A B : Ty Γ}(x : Var A) → Var (A +T B)
\end{code}


A term can be either a variable or a coherence constant ($\mathsf{coh}$).
It encodes all constants for arbitrary types in a contractible context. 

\begin{code}
data Tm where
  var : {Γ : Con}{A : Ty Γ} → Var A → Tm A
  coh : {Γ Δ : Con} → isContr Δ → (δ : Γ ⇒ Δ) → (A : Ty Δ) → Tm (A [ δ ]T)
\end{code}

\AgdaHide{
\begin{code}

{-
-- the symbol is \||


data TyU : Set
data VarU : Set
data TmU : Set


∥_∥Ty : {Γ : Con} → Ty Γ → TyU
∥_∥V : {Γ : Con}{A : Ty Γ} → Var A → VarU
∥_∥Tm : {Γ : Con}{A : Ty Γ} → Tm A → TmU

data TyU where
  *     : TyU
  _=h_  : {A : TyU} → (a b : TmU) → TyU

data VarU where
  v0 : VarU
  vS : VarU → VarU

data TmU where
  var : VarU → TmU
  coh : TyU → TmU


∥ * ∥Ty = *
∥ _=h_ {A} a b ∥Ty =  _=h_ { ∥ A ∥Ty } ∥ a ∥Tm ∥ b ∥Tm

∥_∥Ty-inj : {Γ : Con} → (a b : Ty Γ) → ∥ a ∥Ty ≡ ∥ b ∥Ty → a ≡ b
∥_∥Ty-inj * * refl = refl
∥_∥Ty-inj * (a =h b) ()
∥_∥Ty-inj (a =h b) * ()
∥_∥Ty-inj (_=h_ {A} a b) (_=h_ {A₁} a₁ b₁) eq = {!eq!}


∥ v0 ∥V = v0
∥ vS a ∥V = vS ∥ a ∥V



∥ a ∥Tm = {!!}


data Var'' : {Γ : Con}(A : Ty Γ) → Set where
  v0' : {Γ : Con}{A : Ty Γ}{B : Ty (Γ , A)} -> (B ≡ A +T A)  → Var'' B
  vS' : {Γ : Con}{A B : Ty Γ}{C : Ty (Γ , B)}(x : Var'' A) → (C ≡ A +T B) → Var'' C





∥_∥inj : {Γ : Con}{A : Ty Γ} → (a b : Var A) → ∥ a ∥ ≡ ∥ b ∥ → a ≡ b
∥_∥inj v0 b eq = {!b!}
∥_∥inj (vS a) b eq = {!!}
-}

cohOpV : {Γ : Con}{A B : Ty Γ}{x : Var A}(p : A ≡ B) → var (subst Var p x) ≅ var x
cohOpV {x = x} refl = refl (var x)

cohOpVs : {Γ : Con}{A B C : Ty Γ}{x : Var A}(p : A ≡ B) → var (vS {B = C} (subst Var p x)) ≅ var (vS x)
cohOpVs {x = x} refl = refl (var (vS x))

coh-eq : {Γ Δ : Con}{isc : isContr Δ}{γ δ : Γ ⇒ Δ}{A : Ty Δ} → γ ≡ δ → coh isc γ A ≅ coh isc δ A 
coh-eq refl = refl _

\end{code}
}

With variables defined, it is possible to formalise another core part of the syntactic framework, \emph{contractible
contexts}. Intuitively speaking, a context is contractible if its geometric
realization is contractible to a point. It either contains one variable of the 0-cell $*$ which is the base case, or we can extend a contractible context with a
variable of an existing type and an n-cell, namely a morphism, between the new variable and some existing variable. The graph can be drawn like branching trees.

\begin{code}
data isContr where
  c*   : isContr (ε , *)
  ext  : {Γ : Con} → isContr Γ → {A : Ty Γ}(x : Var A) 
       → isContr (Γ , A , (var (vS x) =h var v0))     
\end{code}

Context morphisms are defined inductively similarly to contexts. A context morphism is a list of terms corresponding to the list of types in the context on the right hand side of the morphism.

\begin{code}
data _⇒_ where
  •    : {Γ : Con} → Γ ⇒ ε
  _,_  : {Γ Δ : Con}(δ : Γ ⇒ Δ){A : Ty Δ}(a : Tm (A [ δ ]T)) 
       → Γ ⇒ (Δ , A)
\end{code}

\AgdaHide{
\begin{code}

hom≡ : {Γ : Con}{A A' : Ty Γ}
                {a : Tm A}{a' : Tm A'}(q : a ≅ a')
                {b : Tm A}{b' : Tm A'}(r : b ≅ b')
                → (a =h b) ≡ (a' =h b')
hom≡ {Γ} {.A'} {A'} {.a'} {a'} (refl .a') {.b'} {b'} (refl .b') = refl


cm-eq : {Γ Δ : Con}{γ δ : Γ ⇒ Δ}{A : Ty Δ}
        {a : Tm (A [ γ ]T)}{a' : Tm (A [ δ ]T)} 
        → γ ≡ δ → a ≅ a' 
        → _≡_ {_} {Γ ⇒ (Δ , A)} (γ , a) (δ , a')
cm-eq refl (refl _) = refl

\end{code}
}


\subsection{Lemmas}

The following lemmas are essential for constructions and theorem proving in later part. We hide the proof of them which can be found in the code.
These four lemmas states that to substitute a type, a variable, a term, or a context morphism with two
context morphisms consecutively, is equivalent to substitute with the composition of the two context morphisms.

\begin{code}
[⊚]T    : {Γ Δ Θ : Con}{A : Ty Θ}{θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}  
        → A [ θ ⊚ δ ]T ≡ (A [ θ ]T)[ δ ]T  

[⊚]v    : {Γ Δ Θ : Con}{A : Ty Θ}(x : Var A){θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}
        → x [ θ ⊚ δ ]V ≅ (x [ θ ]V) [ δ ]tm

[⊚]tm   : {Γ Δ Θ : Con}{A : Ty Θ}(a : Tm A){θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}
        → a [ θ ⊚ δ ]tm ≅ (a [ θ ]tm) [ δ ]tm

⊚assoc  : {Γ Δ Θ Ω : Con}(γ : Θ ⇒ Ω){θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}  
        → (γ ⊚ θ) ⊚ δ ≡ γ ⊚ (θ ⊚ δ)  
\end{code}


\AgdaHide{
\begin{code}

•       ⊚ δ = •
(δ , a) ⊚ δ' = (δ ⊚ δ') , a [ δ' ]tm ⟦ [⊚]T ⟫

\end{code}
}

Weakening inside substitution is equivalent to weakening outside.

\begin{code}
[+S]T   : {Γ Δ : Con}{A : Ty Δ}{δ : Γ ⇒ Δ}{B : Ty Γ} 
        → A [ δ +S B ]T ≡ (A [ δ ]T) +T B 

[+S]tm  : {Γ Δ : Con}{A : Ty Δ}(a : Tm A){δ : Γ ⇒ Δ}{B : Ty Γ}
        → a [ δ +S B ]tm ≅ (a [ δ ]tm) +tm B

[+S]S   : ∀{Γ Δ Δ₁ : Con}{δ : Δ ⇒ Δ₁}{γ : Γ ⇒ Δ}{B : Ty Γ}
        → δ ⊚ (γ +S B) ≡ (δ ⊚ γ) +S B
\end{code}

\todo{maybe hide this part}
There are also some auxiliary functions derived from these lemmas. For instance, the function shown below is used a lot in proofs.

\begin{code}
wk-tm+      : {Γ Δ : Con}{A : Ty Δ}{δ : Γ ⇒ Δ}(B : Ty Γ) 
            → Tm (A [ δ ]T +T B) → Tm (A [ δ +S B ]T)
wk-tm+ B t  = t ⟦ [+S]T ⟫
\end{code}
\todo{maybe hide this part}

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
+T[,]T    : {Γ Δ : Con}{A : Ty Δ}{δ : Γ ⇒ Δ}{B : Ty Δ}{b : Tm (B [ δ ]T)} 
          → (A +T B) [ δ , b ]T ≡ A [ δ ]T

+tm[,]tm  : {Γ Δ : Con}{A : Ty Δ}(a : Tm A){δ : Γ ⇒ Δ}{B : Ty Δ}{c : Tm (B [ δ ]T)}
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
[+S]S {δ = δ , a} = cm-eq [+S]S (cohOp [⊚]T ∾ ([+S]tm a ∾ cong+tm2 [⊚]T) ∾ wk-coh+ -¹)


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

Most of the substitutions are defined as usual, except the one for coherence constants. We do
substitution in the context morphism part of the coherence constants.

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
⊚assoc (_,_ γ {A} a) = cm-eq (⊚assoc γ) 
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
⊚wk (_,_ γ {A} a) = cm-eq (⊚wk γ) (cohOp [⊚]T ∾ (congtm (cohOp [+S]T) ∾ +tm[,]tm a) ∾ cohOp [⊚]T -¹)

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












{-
data Var' : {Γ : Con}(A : Ty Γ) → Set where
  v0 : {Γ : Con}{A : Ty Γ} → Var' {Γ , A} (A +T A)
  vS : {Γ : Con}{A B : Ty Γ}{C : Ty (Γ , A)}(x : Var' (B +T A)) → Var' (B +T A +T C)

open import Data.Empty

var-ne : ∀ (A : Ty ε) → Var {ε} A → ⊥
var-ne A ()

+T-unif : ∀(Γ : Con)(A B C : Ty Γ) → 
          A +T B ≡ C +T B → A ≡ C
+T-unif Γ * B * refl = refl
+T-unif Γ * B (a =h b) ()
+T-unif Γ (a =h b) B * ()
+T-unif Γ (a =h b) B (a₁ =h b₁) eq = {!!}

v0only : ∀ (A : Ty ε) → (x : Var {ε , A} (A +T A)) → x ≡ v0
v0only A x = {!x!}


_≟v_ : ∀(Γ : Con)(A : Ty Γ)(a b : Var A) → Dec (a ≡ b)
_≟v_ .(ε , A) .(A +T A) (v0 {ε} {A}) b = {!b!}
_≟v_ .(Γ , A , A₁) .(A₁ +T A₁) (v0 {Γ , A} {A₁}) b = {!!}
_≟v_ .(Γ , B) .(A +T B) (vS {Γ} {A} {B} a) b = {!!}




var x ≟tm var x₁ = {!!}
var x₁ ≟tm coh x δ A = no (λ ())
coh x δ A ≟tm b = {!b!}

-}






\end{code}
}

\section{Some Important Derivable Constructions}

\input{BasicSyntax2}

\input{Suspension}

\input{BasicLaws}

\input{GroupoidLaws}

\input{Telescopes}

\section{Semantics}

\subsection{Globular Types}

\input{GlobularSets}

%\txa{Can we show that substitution is correct}
%\txa{Some discussion on why we don't need coherence laws.}

\input{Semantics}



\section{Conclusion}

In this paper, we present an implementation of \wog{} following  Brunerie's work. Briefly speaking, we define the syntax of the type theory \tig{}, then a weak $\omega$-groupoid is a globular set with the interpretation of the syntax. To overcome some technical problems, we use heterogeneous equality for terms, some auxiliary functions and loop context in all implementation. We construct the identity morphisms and verify some groupoid laws in the syntactic framework. The suspensions for all sorts of objects are also defined for other later constructions.

There is still a lot of work to do within the syntactic framework. For instance, we would like to investigate the relation between the \tig{} and a Type Theory with equality types and J eliminator which is called $\mathcal{T}_{eq}$. One direction is to simulate the J eliminator syntactically in \tig{} as we mentioned before, the other direction is to derive J using $coh$ if we can prove that the $\mathcal{T}_{eq}$ is a weak $\omega$-groupoid. The syntax could be simplified by adopting categories with families. An alternative may be to use higher inductive types directly to formalize the syntax of type theory. 

We would like to formalise a proof of that Id$\omega$ is a weak $\omega$-groupoid, but the base set in a globular set is an h-set which is incompatible with Id$\omega$. Perhaps we could solve the problem by instead proving a syntactic result, namely that the theory we have presented here and the theory of equality types with J are equivalence. Finally, to model the Type Theory with \wog{} and to eliminate the univalence axiom would be the most challenging task in the future. 




\newpage
\bibliography{my.bib}

\end{document}
