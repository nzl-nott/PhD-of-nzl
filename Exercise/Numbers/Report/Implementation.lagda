\section{Implementation}


\subsection{Proving theorems in Agda}

After getting the numbers defined, we will discuss the approaches and tools used to prove theorems in Agda. Computer-aid formal reasoning is different but has some similarity to the reasoning in regular mathematics. We could omit some common properties like "commutativity" and the target of what the properties are applied to. In the real world, verification is a big problem as everyone will make mistakes and no "checker" will warn you. However to prove theorems in programming languages, although the rules are much stricter so that we have to present each small property used, we will make less mistakes by writing more complete proofs and by using reliable checker who is in charge of verification. In my experience, when I implemented a piece of proof in Agda, I found that I ignored some steps which looks simple but is actually not been proved. However the approaches of proving in Agda are similar to mathematical reasoning. I summarized two ways to organise the proofs which can be mixed used,

\begin{enumerate}
\item \textit{Case analysis -- Pattern match.} For example, natual numbers have two cases, zero and successor of another natural number. In regular mathematics, we could prove proposition of natural numbers using inductive reasoning; In Agda we could use pattern match as below,

\begin{code}
n*0+0=0 : ∀ {n} → n * 0 + 0 ≡ 0
n*0+0=0 {zero} = refl
n*0+0=0 {suc n} = n*0+0=0 {n}
\end{code}

You can see the pattern match is the implementation of case analysis in programming languages according to Curry-Howard correspondence \cite{wiki:Pattern}.

\item \textit{Using lemmas -- Using auxiliary functions.} In regular mathematics, we often prove complicated theorems by proving small lemmas. In programming languages, we can implement this idea trivially by using auxiliary functions. For example,

\begin{code}

ass-lem : ∀ a b c d e f → (a * (+suc b) + c * (+suc d))

+-assoc : Associative _+_
+-assoc (a /suc ad) (b /suc bd) (c /suc cd) = 
  *-cong (ass-lem a bd b ad cd c) \$
  +_ ⋆ ⟨ ℕ.*-assoc (suc ad) (suc bd) (suc cd) ⟩

\end{code}

\end{enumerate}

To use lemmas not only divides huge tasks into small pieces that is easier to prove, but also helps us reduce repeated proofs.


Proving in Agda also has some distinctions with proving in Coq. There is an impredicative universe \emph{Prop} in Coq but not in Agda. The pattern matching mechanism is more flexible in Agda\cite{tutorial}. While in Coq we have tactics to prove the theorems, in Agda we can only write proofs in the form of programs until now. When doing theorem proving we are also equipped with two useful tools,

\begin{enumerate}

\item \textit{Formal reasoning structure.} It is a simulation of the formal reasoning process in regular mathematics. We could prove propositions step by step without using transitivity every time. Every step is explict so that it is more readable. This is an example of using formal reasoning structure,

\begin{code}

begin
  x+ ℕ+ z- ℕ+ (y+ ℕ+ y-)            ≡⟨ exchange x+ z- y+ y- ⟩
  x+ ℕ+ y- ℕ+ (y+ ℕ+ z-)            ≡⟨ eq1 +=' eq2 ⟩
  z+ ℕ+ y- ℕ+ (y+ ℕ+ x-)            ≡⟨ exchange z+ y- y+ x- ⟩
  z+ ℕ+ x- ℕ+ (y+ ℕ+ y-)            ∎

\end{code}

It starts with begin and ends with QED. It allows reflexive refinement during proofs.

\item \textit{Ring solver.} Ring solver is an automatic prover for simple equations which only contains operations including addition, negation, subtraction and multiplication. We can set up ring solver based on the proof of semiring or ring. It is especially helpful for complicated polynomials which have too many elements. To prove a proposition we only need to send it to the solver and the solver will automatically generate the proof we need. However every coin has two sides. Although it saves the time for the programmer it takes much longer time for type-checking. This is an example of how to use ring solver,

\begin{code}

z+0=z : RightIdentity (0 , 0) _+_
z+0=z (a' , b') = solve 2 (λ a b → ...) refl a' b'

\end{code}

\end{enumerate}


\subsection{Problems and Changes}

At first, starting using Agda which was unfamiliar to me is really a big chanllenge. Although it is similar to Coq to some extent, and similar to Haskell which Agda itself is implemented in, it is still a new way to program and do theorem proving. Because of the inadequate understanding of Agda and its library code, I encoutered several problems in undertaking this project.

\subparagraph{Efficiency Problem} The efficiency problem of type checker has been mentioned before. The computation time of type checking is not only related to the amount of the code in a single files but also to the complexity of referenced functions and properties. Therefore although some proofs for rational numbers looks similar to the ones for integers, it takes about double time to check the file. In the other hand, ring solver which is an automatical theorem prover can simplify the proof a lot but also sacrifice the efficiency instead. At first I use the ring solver of natural numbers to prove theorems for setoid integers, it works well but takes more time. However when I try to use the ring solver set up based on the commutative ring of setoid integers, the time spent on type checking is too long to refine the goals. The problem is extremely serious when I use the old version of rational numbers to define real numbers. At that time my computer were working work fully-loaded for about half an hour to make the definition of reals completely checked.

\textit{Changes.} To solve the efficiency problem, firstly I divide large files into more parts such as the field of rational numbers. To reduce computation for type checker I have to give up the ring solver and choose to construct proofs manually. Then I use the formal reasoning structure introduced before. For some properties it is clear and short. But for bigger proofs, the intermediate steps are unecessary to present while they are too long to be structured well. After all I choose to prove theorems without the tools because I can write more compact proofs. Learning from some tricks used in Thomas Anberrée's quotient definition, I using a set of symbols to replace the properties to make them more comprehensive. For example,

\begin{code}

⟨_⟩ : ∀ {A : Set} → Symmetric (_≡_ {A = A})
⟨_⟩ = sym

_>≡<_ : ∀ {A : Set} → Transitive (_≡_ {A = A})
_>≡<_ = trans

_⋆_ : ∀ {A B : Set} (f : A → B)
        {x y} → x ≡ y → f x ≡ f y
_⋆_ = cong

\end{code}

Unary function like "symmetry" can be more meaningful when it includes the equation it applied to. For transitivity, the symbol like a chain links all intermidiate proofs together which are more clearly presented. The congurence is also replaced by a infix operator to make the programs similar to the goals.

Then I revise all the lemmas to generalise the common part and discard useless ones. After rewritting all of them, the proofs become much more shorter and comprehensive with increased effciency to use. For instance, in the older version, to prove the transitivity for rational numbers, I defined 10 lemmas and there are nearly 50 lines of codes. in the new version there are no lemmas for it and the proof is as short as 10 lines. The time spent on type checking the definition with real number is 10 minutes for the older version, but 10 seconds for the newer version.

\subparagraph{Stuck in difficult theorems} For some theorems like the distributivity for normal integers, transitivity for setoid integers and rational numbers and integrity which are comparative much more difficult to prove. At first when I try to prove these properties, I was stuck for very long time. I followed the common steps to pattern match and prove case by case. 
But later I found there are too much cases and the types of goals are beyond my understanding.

To reduce the number of cases, firstly I defined setoid integers and redefined integers as we discussed before. Then I found that to prove lemmas first could also reduce cases. Defining normal integers based on setoid integers makes the proof simpler as well. We can prove theorems of normal integers by proving the ones of setoid integers and proving the isomorphism between the setoid the normal definition. The general quotient theory of Thorsten Altenkirch and Thomas Anberrée could provide easier way to lift theorems, however the current version still has some small questions that restrict it.

The types of goals are always unfolded and unreadable. Therefore I use formal reasoning structure at first. Although I rewrite the code without this tool in the end, it benefited refinement of goals with clear steps. To formalise a proof in Agda, it is better to configure it out in regular mathematics by hand. This is what I have learnt from undertaking this project. It also helps me find mistakes. For example, when I try to prove integrity, I forgot to add the condition of non-zero of the cancelled term. Wrong propositions are allowed to be written but unlikely to be proved. When I try to configure out the proof manually, I found this stupid mistake by trying to replace the cancelled term using 0.

When I explored in the library code, I found there are many useful functions and tools that could simplfy the proofs. To understand these codes more deeply, I tried to write the programs by myself. At the same time, I also learnt a lot from the library code writtern by Nils Anders Danielsson.

\subparagraph{Other problems} There are some other small problems that related to Agda itself. It is better use extraction functions rather than pattern match in defining relations and operations so that they are decoupled with the definition of setoid number,

\begin{definition}
\begin{code}
_∼_ : Rel ℤ₀
(x+ , x-) ∼ (y+ , y-) = (x+ ℕ+ y-) ≡ (y+ ℕ+ x-)

\end{code}
\end{definition}

\begin{definition}
\begin{code}
pos         : ℤ₀ → ℕ
pos (m , _) = m

neg         : ℤ₀ → ℕ
neg (_ , n) = n

_∼_ : Rel ℤ₀
x ∼ y = (pos x ℕ+ neg y) , (pos y ℕ+ neg x)
\end{code}
\end{definition}

However for the secound version, there is problem when using the transitivity proved based on it. Everytime when I use the transitivity I have to explicitly show the three elements involved. For the convenience, I gave up the version with extraction functions.

Also I found when we use "with", we could pattern match on impossible cases. For example, when I pattern match on "suc n", it still requires to prove the case "zero". These problems can be solved by developers of Agda and It will become more powerful in the future. 

During the period of project, Agda has also changed a lot in both itself and its standard library. The relations, operations, algebra strucutures are mostly changed due to the added feature universe polymorphism. It enables programmers to define polymorphic data types on several levels \cite{agdawiki:up}. The pattern match on record is also available right now in the development version $2.2.7$ which will also benefit the theorem proving a lot.