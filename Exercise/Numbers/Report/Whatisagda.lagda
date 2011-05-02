\section{What is Agda?}

Agda is a dependently typed functional programming language. It is designed based on Per Martin-Löf Type Theory \cite{agdawiki:main}. We can find three key elements in the definition of Agda, the "functional programming language", "dependently typed" and "Per Martin-Löf Type Theory".

\begin{itemize}
\item \textit{Functional programming language}. As the name indicates that, functional programming languages emphasizes the application of functions rather than changing data in the imperative style like C++ and Java. The base of functional programming is lambda calculus. The key motivation to develop functional programmming language is to eliminating the side effects which means we can ensure the result will be the same no matter how many times we input the same data. There are several generations of functional programming languages, for example Lisp, Erlang, Haskell etc. Most of the applications of them are currently in the academic fields, however as the functional programming developed, more applications will be explored.

\item \textit{Dependent type}. Dependent types are types that depends on values of other types \cite{dtw}. It is one of the most important features that makes Agda a proof assistant. In Haskell and other Hindley-Milner style languages, types and values are clearly distinct \cite{tutorial}, In Agda, we can define types depending on values which means the border between types and values is vague. To illustrate what this means, the most common example is \textbf{Vector A n}.

\begin{definition}
\begin{code}
data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)
\end{code}
\end{definition}

 It is a data type which represents a vector containing elements of type \textbf{A} and depends on a natural number \textbf{n} which is the length of the list. With the type checker of Agda, we can set more constraints in the type so that type-unmatched problems will always be detected by complier. Therefore we could define the function more precisely as there more partitions of types. For instance, to use the dependently typed vector, it could avoid defining a function which will cause exceptions like out of bounds in Java.

\item \textit{Per Martin-Löf Type Theory}. It has different names like Intuitionistic type theory or Constructive type theory and is developed by Per Martin-Löf in 1980s. It associated functional programs with proofs of mathematical propositions written as dependent types. That means we can now represent propositions we want to prove as types in Agda by dependent types and Curry-Howard isomorphism \cite{aboa}. Then we only need to construct a program of the corresponding type to prove that propostion. For example:

\begin{proposition}
\begin{code}
n+0+0≡n : ∀ {n} → n + 0 + 0 ≡ n
n+0+0≡n {zero} = refl
n+0+0≡n {suc n} = suc n+0+0≡n
\end{code}
\end{proposition}

As Nordström et al. \cite{nps} pointed out that we could express both specifications and programs at the same time when using the type theory to construct proofs using programs. The general approach to do theorem proving in Agda is as follows: First we give the name of the proposition and encode it as the type. Then we can gradually refine the goal to formalise a type-correct program namely the proof. There are no tactics like in Coq. However it is more flexible to construct a proof. The process of building proofs is very similar to the process of constructing proofs in regular mathematics. The logic behind it is that if we could construct an instance of the type (proposition), we prove it. It is actually the Curry-Howard isomorphism.

\end{itemize}

Agda is an extention of this type theory \cite{itt} with some nice features which could benefit the theorem proving,

\begin{itemize}
\item \textit{Pattern matching}. The mechanism for dependently typed pattern matching is very powerful \cite{alti:pisigma-new}. We could prove propositions case by case. In fact it is similar to the approach to prove propositions case by case in regular mathematics. We can also use view to pattern match a condition specially in Agda. For example,
\begin{code}
half : Nat -> Nat
half n with parity n
half .(k * 2)     | even k = k
half .(1 + k * 2) | odd k = k
\end{code}
Here the "parity" after with is a view function that allows us to pattern match on the result of it.

\item \textit{Recursive definition}.The availability of recursive definition enables programmers to prove propositions in the same manner of mathematical induction.  Generally the natural numbers are defined inductively in fucntional programming languages. Then the program of natural numbers can be written using recursive style. There are a lot of types defined using recursive styles in Agda.

\item \textit{Construction of functions}. The construction of functions makes the proving more flexible. We could prove lemmas as we do in maths and reuse them as functions.

\item \textit{Lazy evaulation}. Lazy evaluation could eliminate unecessary operation because it is lazy to delay a computation until we need its result. It is often used to handle infinite data structures. \cite{wiki:Lazy_evaluation}

\end{itemize}

As Agda is primarily used to undertake theorem proofs tasks, the designer enhanced it to be more professional proof assistant. There are several beneficial features facilitating theorem proving,

\begin{itemize}
\item \textit{Type Checker}. Type checker is an essential part of Agda. It is the type checker that detect unmatched-type problem which means the proof is incorrect. It also shows the goals and the environment information related to a proof. Moreover a definition of function must cover all possible cases and must terminate as Agda are not allowed to crash \cite{tutorial}. The coverage checker makes sure that the patterns cover all possible cases \cite{aboa}. And the termination checker will warn possiblily non-terminated error. The missing cases error will be reported by type checker. The suspected non-terminated definition can not be used by other ones. The type checker then ensures that the proof is complete and not been proved by itself. Also we are forced to write the type signature due to the presence of type checker.
 
\item \textit{Emacs interface}. It has a Emacs-based interface for interactively writing and verifying proofs. It allows programmers leaving part of the proof unfinished so that the type-checker will provide useful information of what is missing \cite{aboa}. Therefore programmers could gradually refine their incomplete proofs of correct types.


\item \textit{Unicode support}. It supports Unicode identifiers and keywords like: $\forall$, $\exists$ etc. It also supports mixfix operators like: $+$ , $-$ etc. The benefits are obvious. Firstly we could define symbols which look the same and behave the same in mathematics. These are the expressions of commutativity for natural numbers, the first line is mathematical proposition and the second line is code in Agda:
\begin{code}
∀ a b,  a + b = b + a
∀ a b → a + b = b + a
\end{code}
Secondly we could use symbols to replace some common-used properties to simply the proofs a lot. The following code was simplied using several symbols,
\begin{code}
⟨_⟩ = sym

_>≡<_ = trans

_⋆*_ : ∀ {b c} → b ≡ c → (a : ℕ) →  b * a ≡ c * a
\end{code}

\begin{code}
*-ex :  ∀ a b c → a * (b * c) ≡ b * (a * c)
*-ex a b c = ⟨ *-assoc a b c ⟩ >≡< *-comm a b ⋆* c >≡< *-assoc b a c
\end{code}

Finally, we could use some other languages characters to define functions such as Chinese characters.

\item \textit{Code navigation}. We can simply navigate to the definition of functions from our current code. It is a wonderful features for programmers as it alleviate a great deal of work to look up the library.

\item \textit{Implicit arguments}. We could omit the arguments which could be inferred by the type-checker. In this way, we do not need to present obvious targets of some properties. For example,

\begin{code}
n+0≡n     : ∀ {n} → n + 0 ≡ n

z*0~0 (x+ , x-) =  n+0≡n
\end{code}

The implicit argument in curly bracket is unnecessay to give explicitly when applying this property.


\item \textit{Module system}. The mechanism of parametrised modules makes it possible to define generic operations and prove a whole set of generic properties.

\item \textit{Coinduction}. We could define coinductive types like streams in Agda which are typically infinite data structures. It is a proof technique that could prove the equality satisfied all possible implementation of the specification defined in the codata. It is often used in conjunction with lazy evaluation. \cite{wiki:Coinduction}
	
\end{itemize} 

With these helpful features, Agda has the potentional be a more powerful proof assisstant. Therefore, in order to provide the availability of all the numbers, this project should be beneficial. With the numbers defined and basic properties proven, mathematicians could prove some famous theorems like Fermat’s little theorem then.
