\documentclass[a4paper,12pt]{article}
\def\textmu{}
%include agda.fmt

\usepackage[utf8x]{inputenc}
\usepackage{ucs}
\usepackage{cite}
\usepackage{MnSymbol}


%\DeclareUnicodeCharacter{"2237}{\ensuremath{::}}
\DeclareUnicodeCharacter{"03BB}{\ensuremath{\lambda}}
\DeclareUnicodeCharacter{"03A3}{\ensuremath{\Sigma}}
\DeclareUnicodeCharacter{"03C6}{\ensuremath{\phi}}
\DeclareUnicodeCharacter{"03C8}{\ensuremath{\psi}}
\DeclareUnicodeCharacter{"231C}{\ensuremath{\ulcorner}}
\DeclareUnicodeCharacter{"231D}{\ensuremath{\urcorner}}
\DeclareUnicodeCharacter{"25B6}{\ensuremath{\filledmedtriangleright}}

\usepackage{color}
\newcommand{\txa}[1]{\textcolor{red}{\textbf{Thorsten:~}#1}}

\newcommand{\nzl}[1]{\textcolor{green}{\textbf{Nuo:~}#1}}

\author{Li Nuo}
\title{Investigation into definable quotient types}

\begin{document}

\maketitle

\section{Background}
Quotient generally means the the result of the division. More
abstractly, it represents the result of the partition of sets based on
certain equivalence relation on them. Then can both written as $A/B$,
both of them means divide A by B equally. Similarly, in type theory,
have quotient types. Quotient types are created by dividing types by an equivalence relation.

However in Agda which is the type theory we will talk about cannot
form axiomatic quotient types. But we can still implement the
quotients as setoids containing the carrier the equivalence relation
and the proof of it. We call them definable quotient types and I will
present some examples from my definition for numbers in Agda \cite{myself} to illustrate the ideas.


\section{Quotient definition of Integers}
The integers were invented to represent all the result of subtraction
between natural numbers. Therefore it is naturally to define a pair of
natural numbers to be the result of the subtraction. Hence we can use a pair of natural nubmers as carrier |ℤ₀|.

\begin{code}
ℤ₀ = ℕ × ℕ
\end{code}

When |n1 - n2 = n3 - n4| we can say the quotients |(n1, n2)| and |(n3, n4)| represent the same integer. We can transform the equation to be |n1 + n4 = n3 + n2| so that it becomes a valid judgemental equality between natura numbers. Therefore we can define the equivalence relation of quotient integer as below,


\begin{code}

_∼_ : Rel ℤ₀ zero
(x+ , x-) ∼ (y+ , y-) = (x+ ℕ+ y-) ≡ (y+ ℕ+ x-)

\end{code}

With the euquivalence relation, the set of all pairs of natural
numbers are divided into equivalence classes. For each equivalence class
we need a representative. We can define a normalisation function to
normalise the pair of natural numbers until either of the natural
numbers becomes zero.

\begin{code}


[_]                   : ℤ₀ → ℤ₀
[ m , 0 ]             = m , 0
[ 0 , ℕ.suc n ]       = 0 , ℕ.suc n
[ ℕ.suc m , ℕ.suc n ] = [ m , n ]

\end{code}

For example,  |(3 , 2)| can be normalised to |(2 , 1)|, then to |(1 ,
0)|. 


As soon as we have the normalisation functions, we can use another
more general way to define equivalence relation, namely just identify
their normal form.

\begin{code}

_∼_ : Rel ℤ₀ zero
x ∼ y = [ x ] ≡ [ y ]

\end{code}

The |[ _ ]| is an endomap in the set |ℤ₀|, and the resulting
subset is actually isomorphic to the set of integers. 
However since we
do not distinguish the types of the original form and the normal form,
we lose the information that it has been normalised. Therefore we can
define the type of the result to be the set of integers.


\begin{code}


[_]                   : ℤ₀ → ℤ
[ m , 0 ]             = + m
[ 0 , ℕ.suc n ]       = -suc n
[ ℕ.suc m , ℕ.suc n ] = [ m , n ]

\end{code}


Then this is a retraction function for the normalisation function and
we call it denormalisation function.

\begin{code}

⌜_⌝        : ℤ → ℤ₀
⌜ + n ⌝    = n , 0
⌜ -suc n ⌝ = 0 , ℕ.suc n

\end{code}


Firstly we need to prove |∼| is actually an equivalence
relation.

\emph{Reflexivity}

\begin{code}

zrefl : Reflexive _∼_
zrefl {x+ , x- } = refl

\end{code}

\emph{Symmetry}

\begin{code}

zsym : Symmetric _∼_
zsym {x+ , x- } {y+ , y- } = sym

\end{code}


\emph{Transitivity}

\begin{code}

_>∼<_ : Transitive _∼_
_>∼<_ { x+ , x- } { y+ , y- } { z+ , z- } x=y y=z =
  cancel-+-left (y+ ℕ+ y-)  (ℕ.exchange₁ y+ y- x+ z- >≡<
  (y=z += x=y) >≡< ℕ.exchange₂ z+ y- y+ x-)

\end{code}

\emph{ ∼ isEquivalence relation}

\begin{code}

_∼_isEquivalence : IsEquivalence _∼_
_∼_isEquivalence = record
  { refl  = zrefl
  ; sym   = zsym
  ; trans = _>∼<_
  }

\end{code}


Now we can prove that the |ℤ₀| and its equivalence relation |∼|
form a setoid. 

\emph{ (|ℤ₀|, ∼) is a setoid}

\begin{code}

ℤ-Setoid : Setoid _ _
ℤ-Setoid = record
  { Carrier       = ℤ₀
  ; _≈_           = _∼_
  ; isEquivalence = _∼_isEquivalence
  }

\end{code}

\section{Rational numbers}

The quotient definition of rational number is more natural to
understand and the normalisation is also commonly used in regular
mathematics. We just use one integer and one natural number to
represent a rational number. The reason is because it is hard to
exclude the invalid denominator if we use integers, so I choose the
natural numbers to represent positive natural number which are one bigger.

\begin{code}

data ℚ₀ : Set where
  _/suc_ : (n : ℤ) → (d : ℕ) → ℚ₀

\end{code}

and this is the equivalence relation for it

\begin{code}

_∼_   : Rel ℚ₀ zero
n1 /suc d1 ∼ n2 /suc d2 =  n1 ℤ*ℕ suc d2 ≡ n2 ℤ*ℕ suc d1


\end{code}

\emph{Reflexivity}

\begin{code}

qrefl : Reflexive _∼_
qrefl {n /suc d} = refl

\end{code}

\emph{symmetry}

\begin{code}

qsym : Symmetric _∼_
qsym {a /suc ad} {b /suc bd} = sym

\end{code}

\emph{transitivity}

\begin{code}

qtrans : Transitive _∼_
qtrans {a /suc ad} {b /suc bd} {c /suc cd} a=b b=c with ℤ.0? b
qtrans {a /suc ad} {.(+ 0) /suc bd} {c /suc cd} a=b b=c | yes refl = 
  ℤ.solve0' (+ suc bd) {a} (λ ()) a=b 0~
  ℤ.solve0' (+ suc bd) {c} (λ ()) ⟨ b=c ⟩
qtrans {a /suc ad} {b /suc bd} {c /suc cd} a=b b=c | no ¬p =
  ℤ.l-integrity (b ℤ* (+ suc bd)) (ℤ.nz* b (+ suc bd) ¬p (λ ())) ( 
  ℤ.*-exchange₁ b (+ suc bd) a (+ suc cd) >≡< 
  (ℤ.*-cong b=c a=b) >≡<
  ℤ.*-exchange₂ c (+ suc bd) b (+ suc ad))

\end{code}


\emph{ ∼ isEquivalence relation}

\begin{code}

isEquivalenceℚ₀ : IsEquivalence _∼_
isEquivalenceℚ₀ = record 
  { refl = qrefl
  ; sym  = qsym 
  ; trans = qtrans
  }

\end{code}

Then it is natural to form the setoid

\emph{ (|ℚ₀|, ∼) is a setoid}

\begin{code}

ℚ₀setoid : Setoid _ _
ℚ₀setoid = record {
    Carrier   = ℚ₀
  ;  _≈_      = _∼_
  ; isEquivalence = isEquivalenceℚ₀
  }

\end{code}

However these definition are just setoid and to form a quotient type,
we need more structure. For example, we need a representative for each
equivalence class, we may have a set which is isomorphic to the set of
equivalence classes. Moreover, If we abstract the structure, we can
prove some general properites for definable quotient types.

\section{The general structure of definable quotient types}

I will use the code written by Thomas Amberree in this part. We need
to first establish the quotient signature.

\begin{code}

record QuSig (S : Setoid zero zero) : Set₁ where
             field
                Q     : Set
                [_]   : Carrier S → Q
                sound : ∀ { a b : Carrier S} → (_≈_ S a b) → [ a ] ≡ [ b ]
\end{code}

In this type signature, for certain setoid we have a type represent
the set of the normal form, a map function, and the proof
that it two elements in the |Carrier S|  equal, then they point to the
same element in |Q|.

However, there is no surjective requirements for the map in this signature. If
means we can use the same type for |Carrier S| and |Q|. For example,
for Setoid |ℤ₀, ∼|, we can build a quotient siganature by giving |ℤ₀|
and the endomap normalisation function.


Now, using the quotient signature if we can prove that any function of
type | S → B | respects the equivalence relation, then we can lift it to be
a function of type | Q → B |. Notice that |B| depends on |Q|. Of course we need to prove that it is
lift function. With the lift function we have the first definition of quotient.

\begin{code}


record Qu { S : Setoid zero zero} (QS : QuSig S) : Set₁ where   
              private S      = Carrier S
                      _∼_     = _≈_ S
                      Q      = Q QS
                      [_]    = [_] QS
                      sound  : ∀ { a b : S₀} → (a ∼ b) → [ a ] ≡ [ b ]
                      sound  = sound QS
              field
                lift    : { B : Q → Set }
                        → (f : (a : S) → (B [ a ]))
                        → ((a a' : S) → (p : a ∼ a') → subst B (sound p)  (f a)  ≡  f a')
                        → (c : Q) → B c
                liftok  : ∀ {B a f q}    → lift {B} f q [ a ]  ≡ f a
                liftIrr : ∀ {B a f q q'} → lift {B} f q [ a ]  ≡ lift
                {B} f q' [ a ]

\end{code}

In my opinion the proof irrelevance of lift operations are
unecessary since |lifeok| implies it.

If we have the proof of completeness we know that if two elements in
|S| mapped to the same element in |Q|, they belong to the same
equivalence class. Hence the set of equivalence classes are injective
with respect to the set |Q|. It is an efficient definition of quotient.

\begin{code}
record QuE {S : Setoid zero zero} {QS : QuSig S} (QU : Qu QS) : Set₁ where
       private S      = Carrier S
               _∼_     = _≈_ S
               Q      = Q QS
               [_]    = [_] QS
               sound  : ∀ { a b : S} → (a ∼ b) → [ a ] ≡ [ b ]
               sound  = sound QS
       field
         complete : ∀ {a b : S} → [ a ] ≡ [ b ] → a ∼ b

\end{code}


Otherwise, if we have a embedding function used to choose a representative for
each equivalence class, we can find out the normal form of elements in
|Carrier S|. The proof of stability shows that |emb| is a section of
normalisation function. Since all elements in |Q| fulfill the stability,
the |[_]| must be surjective. The proof |compl| shows that the
representative is in the same equivalence class hence we can prove the
completeness using transitivity. In this definition of quotient, the
set of all equivalence classes are isomorphic to the set |Q|.

\begin{code}
record Nf {S : Setoid zero zero} (QS : QuSig S) : Set₁ where
       private S  = Carrier S
               _∼_   = _≈_ S
               Q     = Q QS
               [_]    = [_] QS
       field
         emb    : Q → S
         compl  : ∀ a → emb [ a ] ∼ a
         stable : ∀ x → [ emb x ]  ≡ x
\end{code}

A quotient with normal form must be efficient. So we can easily
establish the function transforming the |Nf| to |QuE|. The idea to
prove complete is to simply use transitivity to compose the two
|compl| for |a| and |b| .

\begin{code}

nf2quE : {S : Setoid zero zero} → {QS : QuSig S} → {QU : Qu QS} → (Nf QS) → (QuE QU)
nf2quE {S} {QS} {QU} nf = 
    record {
      complete =  λ {a} {b} [a]≡[b] → 
                    ⟨ compl a ⟩ ▶ subst (λ x → x ∼ b) (emb ⋆ ⟨ [a]≡[b] ⟩) (compl b) 
      }
                          where
                          private S      = Carrier S
                                  _∼_     = _≈_ S
                                  Q      = Q QS
                                  [_]    = [_] QS
                                  emb    = emb nf
                                  compl  = compl  nf
                                  ⟨_⟩    : Symmetric _∼_
                                  ⟨_⟩    = symmetric S
                                  _▶_    : Transitive _∼_
                                  _▶_    = transitive S 

\end{code}

We can also establish non-dependent lift version of quotients. We need to prove quotient
induction when we have uniqueness of proof for certain proposition
dependent on |Q|.

\begin{code}
record QuH { S : Setoid zero zero} (QS : QuSig S) : Set₁ where   
              private S   = Carrier S
                      _∼_    = _≈_ S
                      Q      = Q QS
                      [_]     = [_] QS
                      sound  : ∀ { a b : S} → (a ∼ b) → [ a ] ≡ [ b ]
                      sound  = sound QS
              field
                liftH    : { B : Set }
                        → (f : S → B)                                                
                        → ((a a' : S) → (a ∼ a') →  (f a)  ≡  f a')
                        → Q → B
                liftHok  : ∀ {B a f q}    → liftH {B} f q [ a ]  ≡ f a
                -- quotient induction
                qind : (P : Q → Set)  
                       → (∀ {x} → (p p' : P x) → p ≡ p')
                       → (∀ {a} → P [ a ]) 
                       → (∀ {x} → P x )
\end{code}

The normal form definition also implies that we can lift the function
from S to Q.


\begin{code}
nf2qu : {S : Setoid zero zero} → {QS : QuSig S} → (Nf QS) → (Qu QS)
nf2qu {S} {QS} nf = 
        record {
        lift    =  λ {B} f q a⁻ → subst B (stable₀ a⁻) (f (emb₀ a⁻)); 
        liftok  = λ {B} {a} {f} {q} → 
        substIrr B (stable [ a ]) (sound (compl a))  (f (emb [ a ])) ▶ q _ _ (compl a) ;
        liftIrr = refl
        }
        where   S      = Carrier S
                _∼_     = _≈_ S
                [_]    = [_] QS
                sound  : ∀ { a b : S} → a ∼ b → [ a ] ≡ [ b ]
                sound  = sound  QS
                compl  = compl  nf
                stable = stable nf
                emb    = emb    nf

\end{code}

\section{The properties of definable quotient types}

Not only the predicate can be lifted, but also the operators can be
lifted.

\begin{code}


Op : ℕ → Set → Set
Op 0 = λ t → t
Op (suc n) = λ t → (t → Op n t)

record SetoidOp (St : Setoid zero zero)(n : ℕ) : Set₁ where
  constructor §_§
  private
    S = Setoid.Carrier St
  field
    op : Op n S

record QuotientOp {St : Setoid zero zero}
           {Qs : QuSig St}(nf : Nf Qs)(n : ℕ) : Set₁ where
  constructor §_§ 
  private
     Q = QuSig.Q Qs
  field
     op : Op n Q

auxf : {S Q : Set}(n : ℕ)([_] : S → Q)(emb : Q → S) →
          Op n S → Op n Q
auxf zero [_] emb op = [ op ]
auxf (suc n) [_] emb op = λ x → auxf n [_] emb (op (emb x)) 

liftop : {S : Setoid zero zero}(n : ℕ)(Qs : QuSig S)
            (So : SetoidOp S n)(nf : Nf Qs)→ QuotientOp nf n
liftop n (Q , [_] , sound) § op § (emb , compl , stable) = § auxf n
[_] emb op §

\end{code}

We can lift operators of any order within the normal form definition
of quotient type.
According to this, lift the general properties are also possible.


\section{Conclusion}
Here, we only talk about definable quotient types within Agda. The
quotient is a setoid and the elements in an euqivalence classes are
not definitionally equal. However, if we axiomatize the type form of
quotient type and let the Agda automatically normalise the carrier,
then the definitional equality between different elements in same
equivalence class will be present.


\bibliography{quotients}{}
\bibliographystyle{plain}

\end{document}