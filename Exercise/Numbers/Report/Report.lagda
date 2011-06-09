\documentclass{article}
\def\textmu{}
\author{Li Nuo}
\title{Representing numbers in Agda}
\usepackage{dsfont}
\usepackage{amsthm}

%include agda.fmt

\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\theoremstyle{definition}
\newtheorem{definition}{Definition}[section]
\newtheorem{proposition}[theorem]{Proposition}

\DeclareUnicodeCharacter{955}{$\lambda$}
\DeclareUnicodeCharacter{8988}{$\ulcorner$}
\DeclareUnicodeCharacter{8989}{$\urcorner$}
\DeclareUnicodeCharacter{9666}{$\blacktriangleleft$}
\DeclareUnicodeCharacter{9667}{$\triangleleft$}

\begin{document}

\date{May 4, 2010}
\maketitle

\newpage
\tableofcontents

\newpage
\begin{abstract}
Recent development of dependently typed languages like Coq, Agda and Epigram provide programmers as well as mathematicians to prove theorems by writing programs, or more appropirately, constructing proofs. Agda, as one of the latest functional programming languages, is a flexible and convenient proof assisstant equipped with interactive environment for writing and checking proofs. The current version of standard library which is mostly built by Danielsson has included Boolean, algebraic structures, sets, relations etc. However, to prove most of theorems for numbers, it requires more definitions of the numbers beyond natural numbers and more axioms and theorems.
The work is motivated by the numerous good features which gives Agda potential to be a good theorem prover. I will talk about these later along with introducing my code.
 An interesting discovery is that I can understand the natural of numbers more deeply when I use Agda to define numbers.
 
To solve the problem, I start this project, in which I will define the numbers including integers, rational numbers, real numbers and complex numbers and prove the basic properties of them as the tools for theorem proving. There have been some researches in representing numbers especially exact real numbers in other languages, for example Geuvers and Niqui's construction of real numbers in Coq \cite{CRC}, Claire Jones's definition of real numbers in In LEGO \cite{jones}. In this project, I will explore more suitable ways to represent numbers in Agda and try to configure out the construction of real numbers based on Bishop's real number system \cite{bishop}. Although representing numbers in a programming languages must based on the ideas in mathematics, it still has quite a few differences. After we understand the numbers in programming languages, How to implement the definition of numbers in Agda? How to prove properties? What problems and issues that I addressed? What could be extended futher in the future?
\end{abstract}

%include Introduction.lagda

%include Whatisagda.lagda

%include Numbersinmathematics.lagda

%include Numbersincomputerscience.lagda

%include DefineNumbers.lagda

%include Related.lagda

%include Design.lagda

%include Implementation.lagda

%include Evaluation.lagda

%include Summary.lagda

\newpage
\bibliography{myref}
\bibliographystyle{plain}

\end{document}