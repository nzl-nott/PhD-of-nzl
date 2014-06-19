\AgdaHide{
\begin{code}
{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check #-}

module Suspension where

open import BasicSyntax
open import IdentityContextMorphisms
open import Relation.Binary.PropositionalEquality 
open import Data.Product renaming (_,_ to _,,_)
open import Data.Empty
open import Data.Nat


1-1S-same : {Γ : Con}{A B : Ty Γ} → 
            B ≡ A → (Γ , A) ⇒ (Γ , B)
1-1S-same eq = pr1 , pr2 ⟦ congT eq ⟫ 


1-1S-same-T : {Γ : Con}{A B : Ty Γ} → 
               (eq : B ≡ A) → (A +T B) [ 1-1S-same eq ]T ≡ A +T A
1-1S-same-T eq = trans +T[,]T (trans [+S]T (wk-T IC-T))


1-1S-same-tm : ∀ {Γ : Con}{A : Ty Γ}{B : Ty Γ} → 
               (eq : B ≡ A)(a : Tm A) → (a +tm B) [ 1-1S-same eq ]tm ≅ (a +tm A)
1-1S-same-tm eq a = +tm[,]tm a ∾ [+S]tm a ∾ cong+tm (IC-tm a)

1-1S-same-v0 : ∀ {Γ : Con}{A B : Ty Γ} → 
               (eq : B ≡ A) → var v0 [ 1-1S-same eq ]tm ≅ var v0
1-1S-same-v0 eq = wk-coh ∾ cohOp (congT eq) ∾ pr2-v0


_++_ : Con → Con → Con

cor : {Γ : Con}(Δ : Con) → (Γ ++ Δ) ⇒ Δ

repeat-p1 : {Γ : Con}(Δ : Con) → (Γ ++ Δ) ⇒ Γ

Γ ++ ε = Γ
Γ ++ (Δ , A) = Γ ++ Δ , A [ cor Δ ]T


repeat-p1 ε = IdS
repeat-p1 (Δ , A) = repeat-p1 Δ ⊚ pr1


cor ε = •
cor (Δ , A) = (cor Δ +S _) , var v0 ⟦ [+S]T ⟫



_++S_ : ∀ {Γ Δ Θ} → Γ ⇒ Δ → Γ ⇒ Θ → Γ ⇒ (Δ ++ Θ)
cor-inv : ∀ {Γ Δ Θ} → {γ : Γ ⇒ Δ}(δ : Γ ⇒ Θ) → cor Θ ⊚ (γ ++S δ) ≡ δ

γ ++S • = γ
γ ++S (δ , a) = γ ++S δ , a ⟦ trans (sym [⊚]T) (congT2 (cor-inv _)) ⟫ 

cor-inv • = refl
cor-inv (δ , a) = S-eq (trans (⊚wk _) (cor-inv δ)) 
        (cohOp [⊚]T ∾ congtm (cohOp [+S]T) 
        ∾ cohOp +T[,]T 
        ∾ cohOp (trans (sym [⊚]T) (congT2 (cor-inv _))))


id-S++ : {Γ : Con}(Δ Θ : Con) → (Δ ⇒ Θ) → (Γ ++ Δ) ⇒ (Γ ++ Θ)
id-S++ Δ Θ γ = repeat-p1 Δ ++S (γ ⊚ cor _)

\end{code}
}


\subsection{Suspension and Replacement}
\label{sec:susp-and-repl}
%
For an arbitrary type $A$ in $\Gamma$ of level $n$ one can
define a context with $2n$
variables, called the \emph{stalk} of $A$. Moreover one can
define a morphism from $\Gamma$ to the stalk of $A$ such that its
substitution into the maximal type in the stalk of $A$ gives back
$A$. The stalk of $A$ depends only on the level of $A$, the terms in
$A$ define the substitution. Here is an example of stalks of small
levels: $\varepsilon$ (the empty context) for $n=0$; $(x_0 : *, x_1 : *)$ for
$n=1$; $(x_0 : *, x_1 : *, x_2 : x_0\,=_\mathsf{h}\,x_1, x_3 :
x_0\,=_\mathsf{h}\,x_1)$ for $n=2$, etc. 
% \[
% \begin{array}{c@{\hspace{1.5cm}} c@{\hspace{1.5cm}} c@{\hspace{1.5cm}} c@{\hspace{1.5cm}} c@{\hspace{1.5cm}}}
% &&&&6\quad 7\\
% &&&4\quad 5&4 \quad 5\\
% &&2\quad 3&2\quad 3&2\quad 3\\
% &0\quad 1&0\quad 1&0\quad 1&0\quad 1\\
% \\
% n = 0 & n = 1 & n = 2 & n = 3 & n = 4 
% \end{array}
% \]

This is the $\Delta = \varepsilon$ case of a more general construction
where in we \emph{suspend} an arbitrary context $\Delta$ by adding $2n$
variables to the beginning of it, and weakening the rest of the
variables appropriately so that type $*$ becomes $x_{2n-2} =_\mathsf{h}
x_{2n-1}$. A crucial property of suspension is that it preserves
contractibility. 


\subsubsection{Suspension}
\label{sec:susp}

\emph{Suspension} is defined by iteration level-$A$-times the following
operation of one-level suspension. \AgdaFunction{ΣC} takes a
context and gives a context with two new variables of type $*$ added
at the beginning, and with all remaining types in the context suspended
by one level. 

\begin{code}
ΣC : Con → Con
ΣT : ∀{Γ} → Ty Γ → Ty (ΣC Γ)

ΣC ε        = ε , * , *
ΣC (Γ , A)  = ΣC Γ , ΣT A
\end{code}
\noindent The rest of the definitions is straightforward by structural
recursion. In particular we suspend variables, terms and context morphisms:

\begin{code}
Σv   : ∀{Γ}{A : Ty Γ} → Var A → Var (ΣT A)
Σtm  : ∀{Γ}{A : Ty Γ} → Tm A → Tm (ΣT A)
Σs   : ∀{Γ Δ} → Γ ⇒ Δ → ΣC Γ ⇒ ΣC Δ
\end{code}
\AgdaHide{
\begin{code}
*' : {Γ : Con} → Ty (ΣC Γ)
*' {ε} = var (vS v0) =h var v0
*' {Γ , A} = *' {Γ} +T _

ΣT {Γ} * = *' {Γ}
ΣT (a =h b) = Σtm a =h Σtm b

Σs• : (Γ : Con) → ΣC Γ ⇒ ΣC ε
Σs• ε = IdS
Σs• (Γ , A) = Σs• Γ +S _

\end{code}
}
\noindent The following lemma establishes preservation of contractibility by
one-step suspension:

\begin{code}
ΣC-Contr : ∀ Δ → isContr Δ → isContr (ΣC Δ)
\end{code}
\noindent It is also essential that suspension respects weakening and substitution:

\begin{code}
ΣT[+T]   : ∀{Γ}(A B : Ty Γ) 
         → ΣT (A +T B) ≡ ΣT A +T ΣT B

Σtm[+tm] : ∀{Γ A}(a : Tm A)(B : Ty Γ) 
         → Σtm (a +tm B) ≅ Σtm a +tm ΣT B

ΣT[Σs]T  : ∀{Γ Δ}(A : Ty Δ)(δ : Γ ⇒ Δ) 
         → (ΣT A) [ Σs δ ]T ≡ ΣT (A [ δ ]T)
\end{code}
\AgdaHide{
\begin{code}
ΣT[+T] * B = refl
ΣT[+T] (_=h_ {A} a b) B = hom≡ (Σtm[+tm] a B) (Σtm[+tm] b B)

Σv {.(Γ , A)} {.(A +T A)} (v0 {Γ} {A}) = subst Var (sym (ΣT[+T] A A)) v0
Σv {.(Γ , B)} {.(A +T B)} (vS {Γ} {A} {B} x) = subst Var (sym (ΣT[+T] {_} A B)) (vS (Σv x))


Σtm (var x) = var (Σv x)
Σtm (coh x δ A) = coh (ΣC-Contr _ x) (Σs δ) (ΣT A) ⟦ sym (ΣT[Σs]T A δ) ⟫


Σtm-p1 : {Γ : Con}(A : Ty Γ) → Σtm {Γ , A} (var v0) ≅ var v0 
Σtm-p1 A = cohOpV (sym (ΣT[+T] A A))

Σtm-p2 : {Γ : Con}(A B : Ty Γ)(x : Var A) → var (Σv (vS {B = B} x)) ≅ var (vS (Σv x))
Σtm-p2 {Γ} A B x = cohOpV (sym (ΣT[+T] A B))

Σtm-p2-sp : {Γ : Con}(A : Ty Γ)(B : Ty (Γ , A)) → Σtm {Γ , A , B} (var (vS v0)) ≅ (var v0) +tm _
Σtm-p2-sp A B = Σtm-p2 (A +T A) B v0 ∾  cong+tm (Σtm-p1 A)

Σs {Γ} {Δ , A} (γ , a) = (Σs γ) , Σtm a ⟦ ΣT[Σs]T A γ ⟫ 
Σs {Γ} • = Σs• Γ


congΣtm : {Γ : Con}{A B : Ty Γ}{a : Tm A}{b : Tm B} → a ≅ b → Σtm a ≅ Σtm b
congΣtm (refl _) = refl _

cohOpΣtm : ∀ {Δ : Con}{A B : Ty Δ}(t : Tm B)(p : A ≡ B) → Σtm (t ⟦ p ⟫) ≅ Σtm t
cohOpΣtm t p =  congΣtm (cohOp p)


Σs⊚ : ∀ {Δ Δ₁ Γ}(δ : Δ ⇒ Δ₁)(γ : Γ ⇒ Δ) → Σs (δ ⊚ γ) ≡ Σs δ ⊚ Σs γ

Σv[Σs]v :  ∀ {Γ Δ : Con}{A : Ty Δ}(x : Var A)(δ : Γ ⇒ Δ) → Σv x [ Σs δ ]V ≅ Σtm (x [ δ ]V)
Σv[Σs]v (v0 {Γ} {A}) (δ , a) = congtm (Σtm-p1 A) ∾ wk-coh ∾ cohOp (ΣT[Σs]T A δ) ∾ cohOpΣtm a +T[,]T -¹
Σv[Σs]v (vS {Γ} {A} {B} x) (δ , a) = congtm (Σtm-p2 A B x) ∾
                                       +tm[,]tm (Σtm (var x)) ∾
                                       Σv[Σs]v x δ ∾ cohOpΣtm (x [ δ ]V) +T[,]T -¹

Σtm[Σs]tm : ∀ {Γ Δ : Con}{A : Ty Δ}(a : Tm A)(δ : Γ ⇒ Δ) → 
              (Σtm a) [ Σs δ ]tm ≅ Σtm (a [ δ ]tm)
Σtm[Σs]tm (var x) δ = Σv[Σs]v x δ
Σtm[Σs]tm {Γ} {Δ} (coh {Δ = Δ₁} x δ A) δ₁ = congtm (cohOp (sym (ΣT[Σs]T A δ))) 
                      ∾ cohOp (sym [⊚]T) 
                      ∾ coh-eq (sym (Σs⊚ δ δ₁)) 
                      ∾ (cohOpΣtm (coh x (δ ⊚ δ₁) A) (sym [⊚]T) 
                      ∾ cohOp (sym (ΣT[Σs]T A (δ ⊚ δ₁)))) -¹

Σs•-left-id : ∀{Γ Δ : Con}(γ : Γ ⇒ Δ) → Σs {Γ} • ≡ Σs {Δ} • ⊚ Σs γ
Σs•-left-id {ε} {ε} • = refl
Σs•-left-id {ε} {Δ , A} (γ , a) = trans (Σs•-left-id γ) (sym (⊚wk (Σs• Δ)))
Σs•-left-id {Γ , A} {ε} • = trans (cong (λ x → x +S ΣT A) (Σs•-left-id {Γ} {ε} •)) (S-eq (S-eq refl ([+S]V (vS v0) {Σs• Γ} -¹)) ([+S]V v0 {Σs• Γ} -¹))
Σs•-left-id {Γ , A} {Δ , A₁} (γ , a) = trans (Σs•-left-id γ) (sym (⊚wk (Σs• Δ))) 

Σs⊚ • γ = Σs•-left-id γ
Σs⊚ {Δ} (_,_ δ {A} a) γ = S-eq (Σs⊚ δ γ) (cohOp (ΣT[Σs]T A (δ ⊚ γ)) ∾ cohOpΣtm (a [ γ ]tm) [⊚]T ∾ (cohOp [⊚]T ∾ congtm (cohOp (ΣT[Σs]T A δ)) ∾ Σtm[Σs]tm a γ) -¹) 


ΣT[+S]T : ∀{Γ Δ : Con}(A : Ty Δ)(δ : Γ ⇒ Δ)(B : Ty Γ) → ΣT A [ Σs δ +S ΣT B ]T ≡ ΣT (A [ δ ]T) +T ΣT B
ΣT[+S]T A δ B = trans [+S]T (wk-T (ΣT[Σs]T A δ))

ΣsDis : ∀{Γ Δ : Con}{A : Ty Δ}(δ : Γ ⇒ Δ)(a : Tm (A [ δ ]T))(B : Ty Γ) → (Σs {Γ} {Δ , A} (δ , a)) +S ΣT B ≡ Σs δ +S ΣT B , ((Σtm a) +tm ΣT B) ⟦ ΣT[+S]T A δ B ⟫
ΣsDis {Γ} {Δ} {A} δ a B = S-eq refl (wk-coh+ ∾ (cohOp (trans [+S]T (wk-T (ΣT[Σs]T A δ))) ∾ cong+tm2 (ΣT[Σs]T A δ)) -¹)

ΣsΣT : ∀ {Γ Δ : Con}(δ : Γ ⇒ Δ)(B : Ty Γ) → Σs (δ +S B) ≡ Σs δ +S ΣT B
ΣsΣT • _ = refl
ΣsΣT (_,_ δ {A} a) B = S-eq (ΣsΣT δ B) (cohOp (ΣT[Σs]T A (δ +S B)) ∾ cohOpΣtm (a +tm B) [+S]T ∾ Σtm[+tm] a B ∾ cong+tm2 (ΣT[Σs]T A δ) ∾ wk-coh+ -¹) 

*'[Σs]T : {Γ Δ : Con} → (δ : Γ ⇒ Δ) → *' {Δ} [ Σs δ ]T ≡ *' {Γ}
*'[Σs]T {ε} • = refl
*'[Σs]T {Γ , A} • = trans ([+S]T {A = *' {ε}} {δ = Σs {Γ} •}) (wk-T (*'[Σs]T {Γ} •))
*'[Σs]T {Γ} {Δ , A} (γ , a) = trans +T[,]T (*'[Σs]T γ)

ΣT[Σs]T * δ = *'[Σs]T δ
ΣT[Σs]T (_=h_ {A} a b) δ = hom≡ (Σtm[Σs]tm a δ) (Σtm[Σs]tm b δ)

Σtm[+tm] {A = A} (var x) B = cohOpV (sym (ΣT[+T] A B))
Σtm[+tm] {Γ} (coh {Δ = Δ} x δ A) B = cohOpΣtm (coh x (δ +S B) A) (sym [+S]T) ∾ cohOp (sym (ΣT[Σs]T A (δ +S B))) ∾ coh-eq (ΣsΣT δ B) ∾ cohOp (sym [+S]T) -¹ ∾ cong+tm2 (sym (ΣT[Σs]T A δ))


ΣC-Contr .(ε , *) c* = ext c* v0
ΣC-Contr .(Γ , A , (var (vS x) =h var v0)) (ext {Γ} r {A} x) = subst (λ y → isContr (ΣC Γ , ΣT A , y))
                                                                 (hom≡ (cohOpV (sym (ΣT[+T] A A)) -¹)
                                                                  (cohOpV (sym (ΣT[+T] A A)) -¹))
                                                                 (ext (ΣC-Contr Γ r) {ΣT A} (Σv x))
\end{code}}
General suspension to the level of a type $A$ is defined by iteration of
one-level suspension. For symmetry and ease of reading the following
suspension functions take as a parameter a type $A$ in $\Gamma$, while they
depend only on its level. 

\begin{code}
ΣC-it   : ∀{Γ}(A : Ty Γ) → Con → Con

ΣT-it   : ∀{Γ Δ}(A : Ty Γ) → Ty Δ → Ty (ΣC-it A Δ)

Σtm-it  : ∀{Γ Δ}(A : Ty Γ){B : Ty Δ} → Tm B 
        → Tm (ΣT-it A B)
\end{code}
\AgdaHide{
\begin{code}

suspend-S : {Γ Δ Θ : Con}(A : Ty Γ) → Θ ⇒ Δ → (ΣC-it A Θ) ⇒ (ΣC-it A Δ)

ΣC-it * Δ = Δ
ΣC-it (_=h_ {A} a b) Δ = ΣC (ΣC-it A Δ)

ΣT-it * B = B
ΣT-it (_=h_ {A} a b) B = ΣT (ΣT-it A B)
  
Σtm-it * t = t
Σtm-it (_=h_ {A} a b) t = Σtm (Σtm-it A t)

suspend-S * γ = γ
suspend-S (_=h_ {A} a b) γ = Σs (suspend-S A γ)

minimum-S : ∀ {Γ : Con}(A : Ty Γ) → Γ ⇒ ΣC-it A ε

ΣC-p1 :{Γ : Con}(A : Ty Γ) → ΣC (Γ , A) ≡ ΣC Γ , ΣT A
ΣC-p1 * = refl
ΣC-p1 (a =h b) = refl


ΣC-it-p1 : {Γ Δ : Con}(A : Ty Γ)(B : Ty Δ) → ΣC-it A (Δ , B) ≡ (ΣC-it A Δ , ΣT-it A B)
ΣC-it-p1 * B = refl
ΣC-it-p1 (_=h_ {A} a b) B = cong ΣC (ΣC-it-p1 A B)

-- to split ΣC-it

ΣC-it-S-spl' : {Γ Δ : Con}(A : Ty Γ)(B : Ty Δ) → 
               (ΣC-it A Δ , ΣT-it A B) ≡ ΣC-it A (Δ , B)
ΣC-it-S-spl' * B = refl
ΣC-it-S-spl' (_=h_ {A} a b) B = cong ΣC (ΣC-it-S-spl' A B)

ΣC-it-S-spl : {Γ Δ : Con}(A : Ty Γ)(B : Ty Δ) → 
               (ΣC-it A Δ , ΣT-it A B) ⇒ ΣC-it A (Δ , B)
ΣC-it-S-spl * B = IdS
ΣC-it-S-spl (_=h_ {A} a b) B = Σs (ΣC-it-S-spl A B)


ΣC-it-S-spl-¹ : {Γ Δ : Con}(A : Ty Γ)(B : Ty Δ) → 
                ΣC-it A (Δ , B) ⇒ (ΣC-it A Δ , ΣT-it A B)
ΣC-it-S-spl-¹ * B = IdS
ΣC-it-S-spl-¹ (_=h_ {A} a b) B = Σs (ΣC-it-S-spl-¹ A B)


ΣC-it-S-spl2 : {Γ : Con}(A : Ty Γ)
              → (ΣC-it A ε , ΣT-it A * ,  ΣT-it A * +T _) ⇒ ΣC (ΣC-it A ε)
ΣC-it-S-spl2 * = IdS
ΣC-it-S-spl2 (_=h_ {A} a b) = Σs (ΣC-it-S-spl2 A) ⊚ 1-1S-same (ΣT[+T] (ΣT-it A *) (ΣT-it A *))


ΣT-it-wk : {Γ Δ : Con}(A : Ty Γ)(B : Ty Δ) → (ΣT-it A *) [ ΣC-it-S-spl A B ]T ≡ ΣT-it A * +T _
ΣT-it-wk * B = refl
ΣT-it-wk (_=h_ {A} a b) B = trans (ΣT[Σs]T (ΣT-it A *) (ΣC-it-S-spl A B)) (trans (cong ΣT (ΣT-it-wk A B)) (ΣT[+T] (ΣT-it A *) (ΣT-it A B)))

ΣT-it-p1 : ∀ {Γ : Con}(A : Ty Γ) → ΣT-it A * [ minimum-S A ]T ≡ A

ΣT-it-p2 : {Γ Δ : Con}(A : Ty Γ){B : Ty Δ}{a b : Tm B} → ΣT-it A (a =h b) ≡ (Σtm-it A a =h Σtm-it A b)
ΣT-it-p2 * = refl
ΣT-it-p2 (_=h_ {A} _ _) = cong ΣT (ΣT-it-p2 A)


ΣT-it-p3 : {Γ Δ : Con}(A : Ty Γ){B C : Ty Δ} → ΣT-it A (C +T B) [ ΣC-it-S-spl A B ]T ≡ ΣT-it A C +T _ 
ΣT-it-p3 * = trans +T[,]T (wk+S+T IC-T)
ΣT-it-p3 (_=h_ {A} a b) {B} {C} = trans (ΣT[Σs]T (ΣT-it A (C +T B)) (ΣC-it-S-spl A B)) (trans (cong ΣT (ΣT-it-p3 A)) (ΣT[+T] (ΣT-it A C) (ΣT-it A B)))


minimum-S * = •
minimum-S {Γ} (_=h_ {A} a b) = ΣC-it-S-spl2 A ⊚ ((minimum-S A , (a ⟦ ΣT-it-p1 A ⟫)) , (wk-tm (b ⟦ ΣT-it-p1 A ⟫)))


ΣC-it-ε-Contr :  ∀ {Γ Δ : Con}(A : Ty Γ) → isContr Δ → isContr (ΣC-it A Δ)
ΣC-it-ε-Contr * isC = isC
ΣC-it-ε-Contr (_=h_ {A} a b) isC = ΣC-Contr _ (ΣC-it-ε-Contr A isC)


wk-susp : ∀ {Γ : Con}(A : Ty Γ)(a : Tm A) → a ⟦ ΣT-it-p1 A ⟫ ≅ a
wk-susp A a = cohOp (ΣT-it-p1 A)

fci-l1 : ∀ {Γ : Con}(A : Ty Γ) → ΣT (ΣT-it A *) [ ΣC-it-S-spl2 A ]T ≡ (var (vS v0) =h var v0)

fci-l1 * = refl
fci-l1 {Γ} (_=h_ {A} a b) = trans [⊚]T (trans
                                      (congT
                                       (trans (ΣT[Σs]T (ΣT (ΣT-it A *)) (ΣC-it-S-spl2 A))
                                        (cong ΣT (fci-l1 A))))
                                      (hom≡
                                         (congtm (Σtm-p2-sp (ΣT-it A *) (ΣT-it A * +T ΣT-it A *)) ∾
                                          1-1S-same-tm (ΣT[+T] (ΣT-it A *) (ΣT-it A *)) (var v0))
                                         (congtm (Σtm-p1 (ΣT-it A * +T ΣT-it A *)) ∾
                                            1-1S-same-v0 (ΣT[+T] (ΣT-it A *) (ΣT-it A *)))) )

ΣT-it-p1  * = refl
ΣT-it-p1 (_=h_ {A} a b) = trans [⊚]T (trans (congT (fci-l1 A)) (hom≡ (prf a) (prf b)))
  where
    prf : (a : Tm A) → ((a ⟦ ΣT-it-p1 A ⟫) ⟦ +T[,]T ⟫) ⟦ +T[,]T ⟫ ≅ a
    prf a = wk-coh ∾ wk-coh ∾ wk-susp A a
 


Σtm-it-p1 : {Γ Δ : Con}(A : Ty Γ){B : Ty Δ} → Σtm-it A (var v0) [ ΣC-it-S-spl A B ]tm ≅ var v0
Σtm-it-p1 * {B} = wk-coh ∾ cohOp (wk+S+T IC-T)
Σtm-it-p1 (_=h_ {A} a b) {B} = Σtm[Σs]tm (Σtm-it A (var v0)) (ΣC-it-S-spl A B) ∾ congΣtm (Σtm-it-p1 A) ∾ cohOpV (sym (ΣT[+T] (ΣT-it A B) (ΣT-it A B)))



Σtm-it-p2 : {Γ Δ : Con}(A : Ty Γ){B C : Ty Δ}(x : Var B) → (Σtm-it A (var (vS x))) [ ΣC-it-S-spl A C ]tm ≅ Σtm-it A (var x) +tm _
Σtm-it-p2 * x = wk-coh ∾ [+S]V x ∾ cong+tm (IC-v x)
Σtm-it-p2 {Γ} {Δ} (_=h_ {A} a b) {B} {C} x = Σtm[Σs]tm (Σtm-it A (var (vS x))) (ΣC-it-S-spl A C) ∾
                                               congΣtm (Σtm-it-p2 {Γ} {Δ} A {B} x) ∾
                                               Σtm[+tm] (Σtm-it A (var x)) (ΣT-it A C)
\end{code}
}
\noindent Finally, it is clear that iterated suspension preserves contractibility. 

\begin{code}
ΣC-it-Contr  : ∀ {Γ Δ}(A : Ty Γ) → isContr Δ 
             → isContr (ΣC-it A Δ)
\end{code}
\AgdaHide{
\begin{code}
ΣC-it-Contr * x = x
ΣC-it-Contr {Γ}{Δ}(_=h_ {A} a b) x = ΣC-Contr (ΣC-it A Δ) (ΣC-it-Contr A x) 
\end{code}
}
By suspending the minimal contractible context,
*, we obtain a so-called \emph{span}. They are stalks with a top variable added. For example $(x_0: *)$ (the one-variable
context) for $n=0$; $(x_0 : *, x_1 : *, x_2 : x_0\,=_\mathsf{h}\,x_1)$ for
$n=1$; $(x_0 : *, x_1 : *, x_2 : x_0\,=_\mathsf{h}\,x_1, x_3 :
x_0\,=_{\mathsf{h}}\,x_1, x_4 : x_2\,=_\mathsf{h}\,x_3)$ for $n=2$, etc. 
Spans play
an important role later in the definition of composition. 
% Following is a picture of the first few spans for increasing levels $n$ of \AgdaBound{A}.
% \[
% \begin{array}{c@{\hspace{1.5cm}} c@{\hspace{1.5cm}} c@{\hspace{1.5cm}} c@{\hspace{1.5cm}} c@{\hspace{1.5cm}}}
% &&&&8\\
% &&&6&6\quad 7\\
% &&4&4\quad 5&4 \quad 5\\
% &2&2\quad 3&2\quad 3&2\quad 3\\
% 0&0\quad 1&0\quad 1&0\quad 1&0\quad 1\\
% \\
% n = 0&n=1&n=2&n=3&n=4
% \end{array}
% \]

\subsubsection{Replacement}
\label{sec:replacement}

After we have suspended a context by inserting an appropriate number of
variables, we may proceed to a substitution which, so to speak, fills the stalk for
$A$ with $A$. The context morphism representing this substitution is
called $\AgdaFunction{filter}$. In the final step we combine it with
$\Gamma$, the context of $A$.  The new context contains two parts, the
first is the same as $\Gamma$, and the second is the suspended $\Delta$
substituted by $\AgdaFunction{filter}$. However, we also have to drop
the stalk of $A$ becuse it already exists in $\Gamma$.

This operation is called \emph{replacement} because we can interpret it as replacing $*$ in $\Delta$ by
$A$.

As always, we define replacement for contexts, types and terms simultaneously:

\begin{code}
rpl-C   : ∀{Γ}(A : Ty Γ) → Con → Con
rpl-T   : ∀{Γ Δ}(A : Ty Γ) → Ty Δ → Ty (rpl-C A Δ)
rpl-tm  : ∀{Γ Δ}(A : Ty Γ){B : Ty Δ} → Tm B 
        → Tm (rpl-T A B)
\end{code}
Replacement for contexts, $\AgdaFunction{rpl-C}$, defines for a type $A$ in $\Gamma$ and another context $\Delta$ 
a context which begins as $\Gamma$ and follows by each type of $\Delta$ with $*$ replaced with (pasted onto)  $A$. 

\begin{code}
rpl-C {Γ} A ε    = Γ
rpl-C A (Δ , B)  = rpl-C A Δ , rpl-T A B
\end{code}
\noindent To this end we must define the substitution $\AgdaFunction{filter}$ which
pulls back each type from suspended $\Delta$ to the new context. 

\begin{code}
filter  : ∀{Γ}(Δ : Con)(A : Ty Γ) 
        → rpl-C A Δ ⇒ ΣC-it A Δ

rpl-T A B = ΣT-it A B [ filter _ A ]T
\end{code}

\AgdaHide{
\begin{code}
rpl-pr1  : {Γ : Con}(Δ : Con)(A : Ty Γ) → rpl-C A Δ ⇒ Γ

{-
filter : {Γ Δ Θ : Con}(A : Ty Γ) → Θ ⇒ Δ → (rpl-C A Θ) ⇒ (rpl-C A Δ)
-}

rpl-pr1 ε A = IdS
rpl-pr1 (Δ , A) A₁ = rpl-pr1 Δ A₁ +S _



filter ε A = minimum-S A
filter (Δ , A) A₁ =  ΣC-it-S-spl A₁ A ⊚ ((filter Δ A₁ +S _) , var v0 ⟦ [+S]T ⟫)


rpl-T-p1 : {Γ : Con}(Δ : Con)(A : Ty Γ) → rpl-T A * ≡ A [ rpl-pr1 Δ A ]T
rpl-T-p1 ε A = trans (ΣT-it-p1 A) (sym IC-T)
rpl-T-p1 (Δ , A) A₁ = trans [⊚]T (trans (congT (ΣT-it-wk A₁ A)) (trans +T[,]T (trans [+S]T (trans (wk-T (rpl-T-p1 Δ A₁)) (sym [+S]T)))))

rpl-tm A a = Σtm-it A a [ filter _ A ]tm


rpl-tm-id : {Γ : Con}{A : Ty Γ} → Tm A → Tm (rpl-T {Δ = ε} A *)
rpl-tm-id x =  x ⟦ ΣT-it-p1 _ ⟫


rpl-T-p2 : {Γ : Con}(Δ : Con)(A : Ty Γ){B : Ty Δ}{a b : Tm B}  → rpl-T A (a =h b) ≡ (rpl-tm A a =h rpl-tm A b)
rpl-T-p2 Δ A = congT (ΣT-it-p2 A)


rpl-T-p3 : {Γ : Con}(Δ : Con)(A : Ty Γ){B : Ty Δ}{C : Ty Δ}
          → rpl-T A (C +T B) ≡ rpl-T A C +T _
rpl-T-p3 _ A = trans [⊚]T (trans (congT (ΣT-it-p3 A)) (trans +T[,]T [+S]T))

rpl-T-p3-wk : {Γ : Con}(Δ : Con)(A : Ty Γ){B : Ty Δ}{C : Ty Δ}{γ : Γ ⇒ rpl-C A Δ}{b : Tm ((ΣT-it A B [ filter Δ A ]T) [ γ ]T)}
          → rpl-T A (C +T B) [ γ , b ]T ≡ rpl-T A C [ γ ]T
rpl-T-p3-wk Δ A = trans (congT (rpl-T-p3 Δ A)) +T[,]T

rpl-tm-v0' : {Γ : Con}(Δ : Con)(A : Ty Γ){B : Ty Δ}
           → rpl-tm {Δ = Δ , B} A (var v0) ≅ var v0
rpl-tm-v0' Δ A = [⊚]tm (Σtm-it A (var v0)) ∾ congtm (Σtm-it-p1 A) ∾ wk-coh ∾ wk-coh+

rpl-tm-v0 : {Γ : Con}(Δ : Con)(A : Ty Γ){B : Ty Δ}{γ : Γ ⇒ rpl-C A Δ}{b : Tm A}{b' : Tm ((ΣT-it A B [ filter Δ A ]T) [ γ ]T)}
          → (prf : b' ≅ b)
          → rpl-tm {Δ = Δ , B} A (var v0) [ γ , b' ]tm ≅ b
rpl-tm-v0 Δ A prf = congtm (rpl-tm-v0' Δ A) ∾ wk-coh ∾ prf


rpl-tm-vS : {Γ : Con}(Δ : Con)(A : Ty Γ){B C : Ty Δ}{γ : Γ ⇒ rpl-C A Δ}
             {b : Tm (rpl-T A B [ γ ]T)}{x : Var C} → rpl-tm {Δ = Δ , B} A (var (vS x)) [ γ , b ]tm ≅ rpl-tm A (var x) [ γ ]tm
rpl-tm-vS Δ A {x = x} = congtm ([⊚]tm (Σtm-it A (var (vS x))) ∾ (congtm (Σtm-it-p2 A x))  ∾ +tm[,]tm (Σtm-it A (var x))  ∾ ([+S]tm (Σtm-it A (var x)))) ∾ +tm[,]tm (Σtm-it A (var x) [ filter _ A ]tm)

-- basic example

base-1 : {Γ : Con}{A : Ty Γ} → rpl-C A (ε , *) ≡ (Γ , A)
base-1 = cong (λ x → _ , x) (ΣT-it-p1 _)



map-1 : {Γ : Con}{A : Ty Γ} → (Γ , A) ⇒ rpl-C A (ε , *)
map-1 = 1-1S-same (ΣT-it-p1 _)

-- some useful lemmas

rpl*-A : {Γ : Con}{A : Ty Γ} → rpl-T {Δ = ε} A * [ IdS ]T ≡ A
rpl*-A = trans IC-T (ΣT-it-p1 _)

rpl*-a : {Γ : Con}(A : Ty Γ){a : Tm A} → rpl-tm {Δ = ε , *} A (var v0) [ IdS , a ⟦ rpl*-A ⟫ ]tm ≅ a
rpl*-a A = rpl-tm-v0 ε A  (cohOp (rpl*-A {A = A}))

rpl*-A2 : {Γ : Con}(A : Ty Γ){a : Tm (rpl-T A (* {ε}) [ IdS ]T)} 
        → rpl-T A (* {ε , *}) [ IdS , a ]T ≡ A
rpl*-A2 A = trans (rpl-T-p3-wk ε A) rpl*-A

rpl-xy :  {Γ : Con}(A : Ty Γ)(a b : Tm A)
       → rpl-T {Δ = ε , * , *} A (var (vS v0) =h var v0) [ IdS , a ⟦ rpl*-A ⟫ , b ⟦ rpl*-A2 A ⟫ ]T
              ≡ (a =h b)
rpl-xy A a b =  trans (congT (rpl-T-p2 (ε , * , *) A)) 
             (hom≡ ((rpl-tm-vS (ε , *) A)  ∾ rpl*-a A) 
                   (rpl-tm-v0 (ε , *) A (cohOp (rpl*-A2 A))))



rpl-sub : (Γ : Con)(A : Ty Γ)(a b : Tm A) →
          Tm (a =h b)
        → Γ ⇒ rpl-C A (ε , * , * , (var (vS v0) =h var v0))
rpl-sub Γ A a b t = IdS , a ⟦ rpl*-A ⟫ , b ⟦ rpl*-A2 A ⟫ , t ⟦ rpl-xy A a b ⟫
  

\end{code}
}