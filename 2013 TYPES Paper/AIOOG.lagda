\documentclass{article}

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


\newcommand{\wig}{weak $\infty$-groupoids}
\newcommand{\mltt}{Martin-L\"{o}f Type Theory}
\newcommand{\og}{ $\omega$-groupoids}
\newcommand{\wog}{weak $\omega$-groupoids}
\newcommand{\hott}{Homotopy Type Theory}
\newcommand{\ott}{Observational Type Theory}
\newcommand{\tig}{$\mathlarger{\tau} _{\infty-groupoid}$}
\begin{document}
\pagenumbering{gobble}
%\title{An Implementation of Syntactic Weak $\omega$-Groupoids in Agda}
\title{$\omega$-Groupoids and beyond}

\author{Thorsten Altenkirch \and Li Nuo \and Ondrej Rypacek}
\newcommand{\txa}[1]{\marginpar{txa:#1}}

\maketitle


\AgdaHide{
\begin{code}
{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check #-}


module AIOOG where 


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

In \hott{}, a variant of \mltt{}, we reject proof-irrelevance so that the common interpretation of types as setoids has to be generalised. With the univalence axiom, we treat equivalence as equality and interpret types as \og{}. Inspired by Altenkirch's work \cite{txa:csl} and Brunerie's notes \cite{gb:wog}, we study and implement a syntactic definition of Grothendieck \wog{} in Agda which is a popular variant of \mltt{} and a famous theorem prover. It is the first step to model type theory with \wog{} so that we could eliminate the univalence axiom.

\txa{Rewrite abstract at the end}

\end{abstract}


\section{Introduction}

\txa{Rewrite text.}

% Background

%why do we need to use omega groupoid

In Type Theory, a type can be interpreted as a setoid which is a set equipped with an equivalence relation \cite{alt:99}. The equivalence proof of the relation consists of reflexivity, symmetry and transitivity whose proofs are unique. However in \hott{}, we reject the principle of uniqueness of identity proofs (UIP). Instead we accept the univalence axiom which says that equality of types is weakly equivalent to weak equivalence. Weak equivalence can been seen as a refinement of isomorphism without UIP \cite{txa:csl}. To make it more precise, a weak equivalence
between two objects A and B in a 2-category is a morphism $f : A \to B$ which has a
corresponding inverse morphism $ g : B \to A$, but instead of the
proofs of isomorphism $f ∘ g = 1_B$ and  $g ∘ f = 1_A$ we have two
2-cell isomorphisms  $f ∘ g ≅ 1_B$ and  $g ∘ f ≅ 1_A$. 


It has been proved by Vladimir Voevodsky that the univalence axiom implies functional extensionality (a coq proof of this could be found in \cite{uafe}) which results in the problem of non-canonical terms in Type Theory. Altenkirch has proposed a solution in \cite{alt:99} to solve the problem caused by functional extensionality
based on setoid model and also refines it \cite{alti:ott-conf} to \ott{} to justify functional extensionality.
However as mentioned before, setoids require UIP which is incompatible with \hott{}. To solve the problem we should generalise the notion of setoids, namely to enrich the structure of the identity proofs. 



The generalised notion is called Grothendieck \og{}. Grothendieck introduced the notion of \og{} in 1983 in a famous Manuscript \emph{Pursuing Stacks} \cite{gro:ps}. Maltsiniotis continued his work and suggested a simplification of the original definition wihch can be found in \cite{mal:gwog}. Later Ara also present a slight variation of the simplication of \wog{} in \cite{ara:wog}. Categorically
speaking an $\omega$-groupoid is an $\omega$-category in which morphisms on all levels are equivalences. As we know that a set can be seen as a discrete
category, a setoid is a category where every morphism is unique between
two objects. A groupoid is more generalised, every morphism is
isomorphism but the proof of isomorphism is unique, namely the composition of a morphism with its inverse is equal to an identity morphism. Similarly, an
n-groupoid is an n-category in which morphisms on all levels are
equivalence. \og{} which are also called $\infty$-groupoids is an
infinite version of n-groupoids. To model Type Theory without UIP we
also require the equalities to be non-strict, in other words, they are
not definitionally equalities. Finally we should use \wog{} to interpret types and eliminate the univalence axiom.

There are several approaches to formalise \wog{} in Type Theory. For instance, Altenkirch \cite{txa:csl}, and Bruneries' notes \cite{gb:wog}.
This paper mainly explains an implementation of \wog{} following Brunerie's approach in Agda which is a well-known theorem prover and also a variant of intensional \mltt{}. The approach is to specify when a globular set is a weak $\omega$-groupoid by first defining a type theory called \tig{} to describe the internal language
of Grothendieck \wog{}, then interpret it with a globular set and a dependent function. All coherence laws of the \wog{} should be derivable from the syntax, we will present some basic ones, for example reflexivity. One of the main contribution of this paper is to use the heterogeneous equality for terms to overcome some very difficult problems when we used the normal homogeneous one. In this paper, we omit some complicated and less important programs, namely the proofs of some lemmas or the definitions of some auxiliary functions. it is still possible for the reader who is interested in the details to check the code online, in which there are only some minor differences.

\section{Syntax}

\txa{More explanation what is going on}

Since the definitions of contexts, types and terms involve each others, we adopt a more liberal way to do mutual definition in Agda which is a feature available since version 2.2.10. Something declared is free to use even it has not been completely defined.


\paragraph{Basic Objects}

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

Altenkirch also suggests to use Higher Inductive-Inductive definitions for these sets which he coined as Quotient Inductive-Inductive Types (QIIT), in other words, to given an equivalence relation for each of them as one constructor. However we do not use it here.

It is possible to complete the definition of contexts and types first. Contexts are inductively defined as either an empty context or a context with a type of it. Types are defined as either $*$ which we call it 0-cell, or a morphism between two terms of
some type A. If the type A is n-cell then we call the morphism $n+1$-cell. 

\begin{code}
data Con where
  ε   : Con
  _,_ : (Γ : Con)(A : Ty Γ) → Con


data Ty Γ where
  *    : Ty Γ
  _=h_ : {A : Ty Γ}(a b : Tm A) → Ty Γ
\end{code}

\paragraph{Heterogeneous Equality for Terms}

One of the big challenge we encountered at first is the difficulty to formalise and to reason about the equalities of terms.
When we used the common identity types which is homogeneous, we had to use $subst$ function in Agda to unify the types on both sides of the equation. It created a lot of technical issues that made the encoding too involved to proceed. However we found that the syntactic equality of types of given context which will be introduced later, is decidable which means that it is an h-set. In other words, the equalities of types is unique, so that it is safe to use the JM equality (heterogeneous equality) for terms of different types. The equality is inhabited only when they are definitionally equal.

\begin{code}
data _≅_ {Γ : Con}{A : Ty Γ} 
         : {B : Ty Γ} → Tm A → Tm B → Set where
  refl : (b : Tm A) → b ≅ b

\end{code}

\AgdaHide{
\begin{code}
--  We also use different notations for symmetry and transitivity. 

-- sym

_-¹ : ∀{Γ : Con}{A B : Ty Γ}{a : Tm A}{b : Tm B} → a ≅ b → b ≅ a
(refl _) -¹ = refl _

infixr 4 _∾_ 

_∾_ : ∀{Γ : Con}{A B C : Ty Γ}{a : Tm A}{b : Tm B}{c : Tm C} → a ≅ b → b ≅ c → a ≅ c
_∾_ {Γ} {.C} {.C} {C} {.c} {.c} {c} (refl .c) (refl .c) = refl c


\end{code}
}

Once we have the heterogeneous equality for terms, we could define a proof-irrelevant substitution which we call coercion here
since it gives us a term of type A if we have a term of type B and the
two types are equal. We can also prove that the coerced term is heterogeneously equal to the
original term. Combined these definitions, it is much
more convenient to formalise and to reason about term equations.

\begin{code}
_⟦_⟫ : {Γ : Con}{A B : Ty Γ}(a : Tm B) → A ≡ B → Tm A
a ⟦ refl ⟫ = a

cohOp : {Γ : Con}{A B : Ty Γ}{a : Tm B}(p : A ≡ B) 
      → a ⟦ p ⟫ ≅ a
cohOp refl = refl _
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


\end{code}
}


\paragraph{Substitutions}

With context morphism, we could define substitutions for types variables and terms. Indeed the
composition of contexts can be understood as substitution for context morphisms as well.

\begin{code}
_[_]T  : {Γ Δ : Con}(A : Ty Δ)           (δ : Γ ⇒ Δ) → Ty Γ
_[_]V  : {Γ Δ : Con}{A : Ty Δ}(a : Var A)(δ : Γ ⇒ Δ) → Tm (A [ δ ]T)
_[_]tm : {Γ Δ : Con}{A : Ty Δ}(a : Tm A) (δ : Γ ⇒ Δ) → Tm (A [ δ ]T)
_⊚_    : {Γ Δ Θ : Con}      →  Δ ⇒ Θ → (δ : Γ ⇒ Δ) → Γ ⇒ Θ
\end{code}


\paragraph{Weakening Rules}

we could freely add types to the contexts of given any type
judgments, term judgments or context morphisms. We call these rules
weakening rules.

\begin{code}
_+T_  : {Γ : Con}(A : Ty Γ)           → (B : Ty Γ) → Ty (Γ , B)
_+tm_ : {Γ : Con}{A : Ty Γ}(a : Tm A) → (B : Ty Γ) → Tm (A +T B)
_+S_  : {Γ : Con}{Δ : Con}(δ : Γ ⇒ Δ) → (B : Ty Γ) → (Γ , B) ⇒ Δ
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

To define the variables and terms we have to use the weakening rules.
A Term can be either a variable or a J-term. We use the unnamed way
to define variables as either the immediate variable at the right most
of the context, or some variable in the context which can be found by
cancelling the right most variable along with each $vS$. The J-terms are one of the major part of this syntax, which are primitive terms of the primitive types in
contractible contexts which will be introduced later. Since contexts, types, variables and
terms are all mutually defined, most of the properties of them have to be
proved simultaneously as well.


\begin{code}
data Var where
  v0 : {Γ : Con}{A : Ty Γ}              → Var (A +T A)
  vS : {Γ : Con}{A B : Ty Γ}(x : Var A) → Var (A +T B)

data Tm where
  var : {Γ : Con}{A : Ty Γ} → Var A → Tm A
  JJ  : {Γ Δ : Con} → isContr Δ → (δ : Γ ⇒ Δ) → (A : Ty Δ) 
      → Tm (A [ δ ]T)
\end{code}

\AgdaHide{
\begin{code}

cohOpV :  {Γ : Con}{A B : Ty Γ}{x : Var A}(p : A ≡ B) → var (subst Var p x) ≅ var x
cohOpV {x = x} refl = refl (var x)

cohOpVs : {Γ : Con}{A B C : Ty Γ}{x : Var A}(p : A ≡ B) → var (vS {B = C} (subst Var p x)) ≅ var (vS x)
cohOpVs {x = x} refl = refl (var (vS x))

JJ-eq : {Γ Δ : Con}{isc : isContr Δ}{γ δ : Γ ⇒ Δ}{A : Ty Δ} → γ ≡ δ → JJ isc γ A ≅ JJ isc δ A 
JJ-eq refl = refl _

\end{code}
}

Another core part of the syntactic framework is contractible
contexts. Intuitively speaking, a context is contractible if its geometric
realization is contractible to a point. It either contains one variable of the 0-cell $*$ which is the base case, or we can extend a contractible context with a
variable of an existing type and an n-cell, namely a morphism, between the new variable and some existing variable.

\begin{code}
data isContr where
  c*  : isContr (ε , *)
  ext : {Γ : Con} 
      → isContr Γ → {A : Ty Γ}(x : Var A) 
      → isContr (Γ , A , (var (vS x) =h var v0))
\end{code}

Context morphisms are defined inductively similar to contexts. A context morphism is a list of terms corresponding to the list of types in the context on the right hand side of this morphism.

\begin{code}
data _⇒_ where
  •   : {Γ : Con} → Γ ⇒ ε
  _,_ : {Γ Δ : Con}(δ : Γ ⇒ Δ){A : Ty Δ}(a : Tm (A [ δ ]T)) 
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


\paragraph{Lemmas}

The following four lemmas state that to
substitute a type, a variable, a term, or a context morphism with two
context morphisms consecutively, is equivalent to substitute with the
composition of substitution.

\begin{code}
[⊚]T : {Γ Δ Θ : Con}
       {θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}{A : Ty Θ}
       → A [ θ ⊚ δ ]T ≡ (A [ θ ]T)[ δ ]T

[⊚]v : {Γ Δ Θ : Con}
       {A : Ty Θ}(x  : Var A){θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}
          → x [ θ ⊚ δ ]V ≅ (x [ θ ]V) [ δ ]tm

[⊚]tm : {Γ Δ Θ : Con}{A : Ty Θ}(a : Tm A)
        {θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}
        →  a [ θ ⊚ δ ]tm ≅ (a [ θ ]tm) [ δ ]tm

⊚assoc : {Γ Δ Θ Δ₁ : Con}
        (γ : Θ ⇒ Δ₁){θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}
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
[+S]T : {Γ Δ : Con}
        {A : Ty Δ}{δ : Γ ⇒ Δ}
        {B : Ty Γ} 
        → A [ δ +S B ]T ≡ (A [ δ ]T) +T B 

[+S]tm : {Γ Δ : Con}{A : Ty Δ}
         (a : Tm A){δ : Γ ⇒ Δ}
         {B : Ty Γ}
         → a [ δ +S B ]tm ≅ (a [ δ ]tm) +tm B
\end{code}

They are useful to derive some auxiliary functions. The following is one of them which is used a lot in proofs.

\begin{code}
wk-tm+ : {Γ Δ : Con}
         {A : Ty Δ}{δ : Γ ⇒ Δ}
         (B : Ty Γ) 
         → Tm (A [ δ ]T +T B) → Tm (A [ δ +S B ]T)
wk-tm+ B t = t ⟦ [+S]T ⟫
\end{code}

\AgdaHide{

\begin{code}
•       +S B = •
(δ , a) +S B = (δ +S B) , wk-tm+ B (a +tm B)


[+S]T {A = *}     = refl
[+S]T {A = a =h b} = hom≡ ([+S]tm a) ([+S]tm b)

\end{code}
}

We could cancel the last term in the substitution for weakened objects
since weakening doesn't introduce new variables in types and terms.

\begin{code}
+T[,]T : {Γ Δ : Con}
         {A : Ty Δ}{δ : Γ ⇒ Δ}
         {B : Ty Δ}{b : Tm (B [ δ ]T)} 
         → (A +T B) [ δ , b ]T ≡ A [ δ ]T

+tm[,]tm : {Γ Δ : Con}{A : Ty Δ}
         (a : Tm A){δ : Γ ⇒ Δ}{B : Ty Δ}
         {c : Tm (B [ δ ]T)}
         → (a +tm B) [ δ , c ]tm ≅ a [ δ ]tm 
\end{code}

\AgdaHide{
\begin{code}

(var x)     +tm B = var (vS x)
(JJ cΔ δ A) +tm B = JJ cΔ (δ +S B) A ⟦ sym [+S]T ⟫ 



cong+tm : ∀ {Γ : Con}{A B C : Ty Γ}{a : Tm A}{b : Tm B}→ a ≅ b → a +tm C ≅ b +tm C
cong+tm (refl _) = refl _

cong+tm2 : ∀ {Γ : Con}{A B C : Ty Γ}{a : Tm B}(p : A ≡ B) → a +tm C ≅ a ⟦ p ⟫ +tm C
cong+tm2 refl = refl _

wk-T : {Δ : Con}
       {A B C : Ty Δ}
       → A ≡ B → A +T C ≡ B +T C
wk-T refl = refl


wk+S+T : ∀{Γ Δ : Con}{A : Ty Γ}{B : Ty Δ}{γ}{C} → A [ γ ]T ≡ C → A [ γ +S B ]T ≡ C +T B
wk+S+T eq = trans [+S]T (wk-T eq)

wk+S+tm : ∀{Γ Δ : Con}{A : Ty Γ}{B : Ty Δ}(a : Tm A){C : Ty Δ}{γ : Δ ⇒ Γ}{c : Tm C} → a [ γ ]tm ≅ c → a [ γ +S B ]tm ≅ c +tm B
wk+S+tm _ eq = [+S]tm _ ∾ cong+tm eq



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
wk-hom+ = hom≡ wk-coh+ wk-coh+  -- [+S]T

wk-⊚ : {Γ Δ Θ : Con}
       {θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}{A : Ty Θ}
       → Tm ((A [ θ ]T)[ δ ]T) → Tm (A [ θ ⊚ δ ]T)
wk-⊚ t = t ⟦ [⊚]T ⟫

[⊚]T {A = *} = refl
[⊚]T {A = _=h_ {A} a b} = hom≡ ([⊚]tm _) ([⊚]tm _) 

+T[,]T {A = *} = refl
+T[,]T {A = _=h_ {A} a b} = hom≡  (+tm[,]tm _) (+tm[,]tm _)

\end{code}
}

Most of the substitutions are defined as usual, except the one for J-terms. We do
substitution in the context morphism part of the J-terms.

\begin{code}

var x     [ δ ]tm = x [ δ ]V
JJ cΔ γ A [ δ ]tm = JJ cΔ (γ ⊚ δ) A ⟦ sym [⊚]T ⟫

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


⊚assoc • = refl
⊚assoc (_,_ γ {A} a) =
  cm-eq (⊚assoc γ) 
    (cohOp [⊚]T 
    ∾ (congtm (cohOp [⊚]T)
    ∾ ((cohOp [⊚]T 
    ∾ [⊚]tm a) -¹)))



[⊚]v (v0 {Γ₁} {A}) {θ , a}  = wk-coh ∾ cohOp [⊚]T ∾ congtm (cohOp +T[,]T -¹) 
[⊚]v (vS {Γ₁} {A} {B} x) {θ , a}  = 
  wk-coh
  ∾ ([⊚]v x
    ∾ (congtm (cohOp +T[,]T) -¹))



[⊚]tm (var x) = [⊚]v x
[⊚]tm (JJ c γ A) = cohOp (sym [⊚]T) ∾ (JJ-eq (sym (⊚assoc γ)) ∾ cohOp (sym [⊚]T) -¹) ∾ congtm (cohOp (sym [⊚]T) -¹)


⊚wk : ∀{Γ Δ Δ₁}{B : Ty Δ}(γ : Δ ⇒ Δ₁){δ : Γ ⇒ Δ}{c : Tm (B [ δ ]T)} → (γ +S B) ⊚ (δ , c) ≡ γ ⊚ δ
⊚wk • = refl
⊚wk (_,_ γ {A} a) = cm-eq (⊚wk γ) (cohOp [⊚]T ∾ (congtm (cohOp [+S]T) ∾ +tm[,]tm a) ∾ cohOp [⊚]T -¹)

+tm[,]tm (var x) = cohOp +T[,]T
+tm[,]tm (JJ x γ A) = congtm (cohOp (sym [+S]T)) ∾ cohOp (sym [⊚]T) ∾ JJ-eq (⊚wk γ) ∾ cohOp (sym [⊚]T) -¹



[+S]V : {Γ Δ : Con}{A : Ty Δ}
         (x : Var A){δ : Γ ⇒ Δ}
         {B : Ty Γ}
         → x [ δ +S B ]V ≅ (x [ δ ]V) +tm B
[+S]V v0 {_,_ δ {A} a} = wk-coh ∾ wk-coh+ ∾ cong+tm2 +T[,]T
[+S]V (vS x) {δ , a} = wk-coh ∾ [+S]V x ∾ cong+tm2 +T[,]T

lem+Stm : ∀{Γ Δ Δ₁ : Con}(δ : Δ ⇒ Δ₁)(γ : Γ ⇒ Δ)(B : Ty Γ) → δ ⊚ (γ +S B) ≡ (δ ⊚ γ) +S B
lem+Stm • γ B = refl
lem+Stm (_,_ δ {A} a) γ B = cm-eq (lem+Stm δ γ B) (cohOp [⊚]T ∾ ([+S]tm a ∾ cong+tm2 [⊚]T) ∾ wk-coh+ -¹)



[+S]tm (var x) {δ} {B} = [+S]V x
[+S]tm (JJ x δ A) {γ} {B} = cohOp (sym [⊚]T) ∾ JJ-eq (lem+Stm δ γ B) ∾ cohOp (sym [+S]T) -¹ ∾ cong+tm2 (sym [⊚]T)

\end{code}
}

\section{Some Important Derivable Constructions}

\txa{Needs to be reordered, and better explained}

\input{AIOOGS2}
\input{GroupoidLaws}



\input{Suspension}

\txa{Prove the laws of groupoid. Maybe even some higher order?}

\section{Semantics}

\paragraph{Globular Sets}

\input{GlobularSets}

\txa{Can we show that substitution is correct}
\txa{Some discussion on why we don't need coherence laws.}

\input{Semantics}
% relation with categories with families

% different ideas of how to do solve refl



\section{Conclusion}

In this paper, we present an implementation of \wog{} following the Brunerie's work. Briefly speaking, we define the syntax of the type theory \tig{}, then a weak $\omega$-groupoid is a globular set with the interpretation of the syntax. To overcome some technical problems, we use heterogeneous equality for terms, some auxiliary functions and loop context in all implementation. We construct the identity morphisms and verify some groupoid laws in the syntactic framework. The suspensions for all sorts of objects are also defined for other later constructions.

There are still a lot of work to do within the syntactic framework. For instance, we would like to investigate the relation between the \tig{} and a Type Theory with equality types and J eliminator which is called $\mathlarger{\tau}_{eq}$. One direction is to simulate the J eliminator syntactically in \tig{} as we mentioned before, the other direction is to derive J using $Coh$ if we can prove that the $\mathlarger{\tau}_{eq}$ is a weak $\omega$-groupoid. The syntax could be simplified by adopting categories with families. Altenkirch also suggests to use explicit substitution and QIIP which is an alternative way to define the syntax. 

We would like to formalise a proof of that Id$\omega$ is an \wog{}, but the base set in a globular set is an h-set which is incompatible with Id$\omega$. Perhaps we could solve the problem by making a syntactic proof. Finally, to model the Type Theory with \wog{} and to eliminate the univalence axiom would be the most challenging task in the future. 






\newpage
\bibliography{my}
\bibliographystyle{plain}

\end{document}
