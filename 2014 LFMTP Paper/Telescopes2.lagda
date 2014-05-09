\AgdaHide{
\begin{code}
{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check #-}

module Telescopes2 where

open import Relation.Binary.PropositionalEquality 
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat

open import BasicSyntax renaming (_∾_ to htrans)
open import IdentityContextMorphisms
open import Suspension
open import GroupoidStructure
\end{code}
}
\subsection{Higher Structure} In the previous text we have shown how
to define 1-groupoid structure on an arbitrary level. Here we indicate
how all levels also bear the structure of $n$-groupoid for arbitrary
$n$. The rough idea amounts to redefining telescopes of \cite{txa:csl}
in terms of appropriate contexts, which are contractible, and the different
constructors for terms used in \cite{txa:csl} in terms of
$\mathsf{coh}$.

To illustrate this we consider the simpler example of higher
identities. Note that the domain and codomain of $n\text{+}1$-iterated
identity are $n$-iterated identities. Hence we proceed by induction on
$n$. Denote a span of depth $n$ $S_n$. Then there is a chain of
context morphisms $S_0 \Rightarrow S_1 \Rightarrow \cdots \Rightarrow
S_n$. Each $S_{n+1}$ has one additional variable standing for the
identity iterated $n\text{+}1$-times. Because $S_{n+1}$ is contractible, one
can define a morphism $S_n \Rightarrow S_{n+1}$ using $\AgdaInductiveConstructor{coh}$
to fill the last variable and variable terms on the first $n$
levels. By composition of the context morphisms one defines $n$ new
terms in the basic one variable context $*$ -- the iterated
identities. Using suspension one can lift the identities to an
arbitrary level.

Each $n$-cell has $n$-compositions. In the case of
2-categories, 1-cells have one composition, 2-cells have vertical and
horizontal composition. Two 2-cells are horizontally composable only
if their 1-cell top and bottom boundaries are composable. The boundary
of the composition is the composition of the boundaries.  Thus for
arbitrary $n$ we proceed using a chain of $V$-shaped contractible
contexts. That is contexts that are two spans conjoined at the base
level at a common middle variable. Each successive composition is
defined using contractibility and \AgdaInductiveConstructor{coh}.

To fully imitate the development in \cite{txa:csl}, one would
also have to define all higher coherence laws. But the sole purpose
of giving an alternative type theory in this paper is to avoid that. 
