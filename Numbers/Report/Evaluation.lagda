\section{Evaluation}

\subsection{How to use the code}

Most of the code are tested to worked under Agda $2.2.6$ except the definitions of normal rational number and real number. These two definitions use the pattern match of record type which is only available from $2.2.7$ version which is a development version.

To use the numbers it is enough to just import the definition file of each type of numbers. What should be noted is that, the setoid definitions require the "Data.Product" library code and In all kinds of these numbers, "Data.Nat" which includes the definition of natural numbers is also essential. According to the dependencies, we should include the lower level of numbers if we want use the higher level ones.

To prove the properties, it is enough to just import the second part to use the ring solver for simple propositions. In addition we should add the following code,
\begin{code}
open RingSolver
   using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)
\end{code}

I have tested the ring solvers of each type of numbers. For example,

\begin{code}
t : ∀ a b c d → (a + b) * (c + d) ∼ a * c + a * d + b * c + b * d
t = solve 4 
    (λ a b c d → (a :+ b) :* (c :+ d) := a :* c :+ a :* d :+ b :* c :+ b :* d)
    zrefl
\end{code}

It takes about one minute to verify the correctness of the proof. Ring solver is a good choice for proving unusual used propositions.

Importing the "Properties" files, we could construct the proof manually. Some symbols for generic properties are defined in one single file "Symbols".

\subsection{Feedback}

I have changed the naming convention, organisation of files, layout of code and improve the readability of the code based on the feedback from Nils Anders Danielsson who is the main designer of the standard library of Agda.
I also get some feedback from some friends of mine who have knowledge of Agda. The feedbacks reflect some problems,

\begin{itemize}
\item \textit{The definitions is hard to understand.} The definition requires more knowledge beyond the simple mathematics, especially for the real numbers, which seems difficult to use. I think the problem could be solved with reading the discussion of definitions of real numbers.

\item \textit{Ring solver.} It is quite slow compared to what they have exprienced before but is still acceptable. The positive aspect is that they find it is interesting and helpful to use ring solver.

\item \textit{Description.} The explanation for each property facilitates the understanding of the code. But if the emacs interface could fold the description with a button, the code will look clearer.

\end{itemize}
