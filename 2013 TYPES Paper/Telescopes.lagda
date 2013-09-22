
\AgdaHide{
\begin{code}
{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check #-}

module Telescopes where

open import Relation.Binary.PropositionalEquality 
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat

open import AIOOG renaming (_∾_ to htrans)
open import AIOOGS2
open import Suspension
open import GroupoidLaws
\end{code}
}

\section{Higher Structure}

\subsection{Spans}
\label{sec:spans}

For each $n\in \mathbf{N}$, we define a context $S_n$ called
\emph{span} which has $2n+1$ variables organised in such a way that
\begin{itemize}
\item the \emph{type} of variables $0$ and $1$ is $\ast$ 
\item the type of each variable $k>1$ is $\lfloor k / 2 \rfloor -1 
  =_\mathsf{h} \lfloor k / 2 \rfloor$
\item to each variable $k$ we assign a \emph{level} as $\lfloor k / 2 \rfloor$
\end{itemize}
%
So except for the top level, $n$, there are two variables on each
level whose type is the equality type of the two variables on the
level below, except for the bottom-level variables which are, of
course, of type $\ast$. Here is a picture of the first few spans where
the ordering of the variables is suggestive of their levels and types.
\[
\begin{array}{c@{\hspace{1.5cm}} c@{\hspace{1.5cm}} c@{\hspace{1.5cm}} c@{\hspace{1.5cm}} c@{\hspace{1.5cm}}}
&&&&8\\
&&&6&6\quad 7\\
&&4&4\quad 5&4 \quad 5\\
&2&2\quad 3&2\quad 3&2\quad 3\\
0&0\quad 1&0\quad 1&0\quad 1&0\quad 1\\
\\
S_0&S_1&S_2&S_3&S_4
\end{array}
\]
%
In each case we call the sole variable at level $n$ the
\emph{peak}. Note that each $S_n$ is contractible because $S_0$ is
trivially, and $S_{n+1}$ arises from $S_n$ by addition of one new
variable and another variable into it, exactly as \textsf{ext} of
\textsf{isContr} requires. We call the proof of $S_n$'s contractibility 
$\mathsf{is\text{-}contr}\,S_n$. 

In each $S_n$ define the type $\sigma_n$ as $2n-2
~=_\mathsf{h}~2n-1$. We are going to show that the following 
\[
S_0 \three/<-`>`<-/^{s_0}|{i_0}_{t_0} S_1 \three/<-`>`<-/^{s_1}|{i_1}_{t_1} S_2 \cdots S_n
\three/<-`>`<-/^{s_n}|{i_n}_{t_n} S_{n+1} \cdots
\]
is a \emph{reflexive globular object} in $\mathsf{Con}$, the category
of contexts and context morphisms. I.e. that it satisfies the
following (usual) \emph{globular identities}:
\begin{equation}\label{eq:glob}
\begin{array}{rl}
s_n t_{n+1}&~=~s_n s_{n+1}\\
t_n t_{n+1}&~=~t_n s_{n+1}
\end{array}
\end{equation}
% 
together with
\begin{equation}
  \label{eq:refl-glob}
  s_n i_n ~= ~\mathsf{id}~=~ t_ni_n
\end{equation}

For each $n$, define context morphisms $s_n, t_n  : S_{n+1}
\Rightarrow S_n$ by the substitutions
\begin{align*}
s_n &~=~& k &~\mapsfrom~k &k < 2n\\
&&2n &~\mapsfrom~2n \\
t_n &~=~& k &~\mapsfrom~k &k < 2n\\
&&2n &~\mapsfrom~2n+1
\end{align*}
%
In words, $s_n$ forgets the last two variables of $S_{n+1}$ and
$t_n$ forgets the peak and its domain. It's easy to check that $s$ and
$t$ indeed satisfy \eqref{eq:glob}.


In order to define $i_n :  S_n \Rightarrow S_{n+1}$, 
we must consider contexts $\overline{S_n}$ which are like
$S_n$ without the last variable, together with types
$\overline{\sigma}_n$ which are like $\sigma_n$ but considered in the
smaller context: 
%
\[
\begin{array}{c@{\hspace{1.5cm}} c@{\hspace{1.5cm}} c@{\hspace{1.5cm}} c@{\hspace{1.5cm}} c@{\hspace{1.5cm}}}
&&&&6\quad 7\\
&&&4\quad 5&4 \quad 5\\
&&2\quad 3&2\quad 3&2\quad 3\\
&0\quad 1&0\quad 1&0\quad 1&0\quad 1\\
\\
\overline{S}_0&\overline{S}_1&\overline{S}_2&\overline{S}
_3&\overline{S}_4
\end{array}
\]
%
For each $n$ there is a context morphism $\overline{i_n}: S_n
\Rightarrow \overline{S}_{n+1}$ defined by
\begin{align*}
\overline{i_n} &~=~& k &~\mapsfrom ~ k & k \le 2n\\
&& 2n+1 &~\mapsfrom~2n 
\end{align*}
%
The substitution of $\overline{\sigma}_{n+1}$ along $\overline{i_n}$,
$\overline{i_n}[\overline{\sigma}_{n+1}]_\mathsf{T}$, is equal to $n
=_\mathsf{h} n$ in $S_n$. So in order to extend $\overline{i_n}$ to
$i_n : S_n \Rightarrow S_{n+1}$ we must define a term in
$\overline{i_n}[\overline{\sigma}_{n+1}]_\mathsf{T}$.  We can
readily do that by $\mathsf{JJ}$:
\[
i_n~ = ~ \overline{i_n}\, ,
\,\mathsf{JJ}~(\mathsf{IdCm\,S_n})~(2n\,=_\mathsf{h}\,2n)~(\mathsf{is\text{-}contr}~S_n)
\]
\noindent It's easy to check that $i_n$ satisfies \eqref{eq:refl-glob}. 

For each $n$ consider the chain 
\[S_0 \to^{i_0} S_1 \to^{i_1} S_2 \to \cdots \to^{i_{n-1}} S_n\]
%
The substitution
$\sigma_n[i_0]_\mathsf{T}\cdots[i_{n-2}]_\mathsf{T}[i_{n-1}]_\mathsf{T}
\equiv \sigma_n[i_{n-1}\cdots i_0]_\mathsf{T}$ is
a type, $\lambda_n$, in $S_0$.
We call $\lambda_n$ the \emph{n\text{-}iterated loop type} on 
$0$. The term $(2n) [i_{n-1}\cdots i_0]_\mathsf{tm}$ is
the iterated identity term on $0$. 

\subsection{Composition}
\label{sec:composition}
%
