\section{Related work}

\subsection{The integers and rational numbers in Coq}
Coq which is also a proof assistant has developed a more completed library. There is a binary integer definition written by Pierre Crégut. The integer defines on a binary positive natural number as follows,
\begin{definition}
\begin{code}
Inductive positive : Set :=
| xI : positive -> positive
| xO : positive -> positive
| xH : positive.
\end{code}
\end{definition}
It defines positive natural numbers in binary notation. XH represents 1, XI p represents p 1, and XO represents p 0. For example, XI (XO XH) represents 101 binary number, namely 5.
Then the integers could be defined as 
\begin{definition}
\begin{code}
Inductive Z : Set :=
| Z0 : Z
| Zpos : positive -> Z
| Zneg : positive -> Z. 
\end{code}
\end{definition}
This definition is symmetric. ZO is 0, Zpos maps positives just inject positive natural numbers to positive integers, and Zneg constructs negative integers from positives. The operations are defined based on the operation of binary numbers. It is quite different to what I do in this project although the definition looks similar. Alternatively, there are also 31-bits integers designed to achieve hardware-efficient computations encoded by A. Spiwack.

In the definition of rational number, the advantage of define positives is enhanced as we only need a integer and positive to represent rational numbers in fractional forms. The other parts are quite similar to what I have done such as the definition of equivalence. Because the rational number is not in reduced form, it is also a setoid definition. The designer also prove the necessary properties for rational numbers. What is distinct is the field tactics are defined in the library. In addition there is a canonical representation of rational numbers which consists of the setoid definition and a proof that it is the same with its simplification. It is just an alternative way to write the normal form of rational numbers.


\subsection{The real numbers in Coq}
The construction of real numbers in Coq standard library are axiomatized (refer to the Coq standard library). It defines R as a parameter and the relations and operations based on the classical axioms of real numbers. Namely all the basic properties for proving are axioms like the regular mathematics.

Geuvers and Niqui \cite{CRC} implements real numbers in a different way in Coq. Their work is backward developed. First they define real numbers and properties as axioms. Then they define rational numbers and real numbers based on the Cauchy sequence of $\mathds{Q}$. What they need to prove is this construction satisfy the set of axioms they defined. They also prove their axioms are equivalent to the ones in \cite{Bridges199995}.

Another approach to define reals in Coq is introduced by A. Ciaffaglione and P. Di Gianantonio \cite{Ciaffaglione200639}. They construct the reals using infinite streams by coinductive approach which is also available in Agda. They put emphasis on the efficiency of implementation. 

Russell O’Connor \cite{oconnor} also build real number constructively based on implementation of compelte metric spaces. The basic functions and proofs are also included. Finally he also implement an automatical proving tatic for strict inequalities for real numbers.

\subsection{The real numbers in other languages}
There are also some brilliant constructions in other type theoretic proof assistants such as LEGO and NuPrl. 
\begin{itemize}

\item In LEGO, Claire Jones \cite{jones} builds a real number as a collection of arbitrary small nested intervals with rational endpoints. It mainly focus two main areas, one is the construction of real numbers, the other is the compeletion of metric space. 

\item In NuPrl, J Chirimar, D Howe \cite{howe} firstly defines rational number and then defines the reals using regular Cauchy sequences also following Bishop's construction \cite{bishop}. Finally they prove the Cauchy completeness of reals namely all Cauchy sequence converge.

\item In HOL, John Harrison adopted another construction of real numbers, the dedekind cut. It has potential to be implented and tested in Agda to use dedekind cut method.

\item Pietro Di Gianantonio \cite{pdg} proposed an implementation of the real numbers by using the feature of functional programming languages, lazy evaluation which is also available in Agda. It discuss the computability of real numbers represented by infinite digits and related it to the domain theory.

\end{itemize}

These definitions explore different ways to represent real numbers more deeply and widely. The construction of integers and rational numbers are mostly similar except the binary and inaccurate digits representations. For real numbers, the Cauchy sequence with metric space is choosen primarily. There is various implementation of real numbers in most of the theorem prover.