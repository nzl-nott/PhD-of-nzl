
\AgdaHide{
\begin{code}
module IdentityContextMorphisms where


open import BasicSyntax
open import Relation.Binary.PropositionalEquality 
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat

\end{code}
}
\newcommand{\Tm}{\mathsf{Tm}}
\newcommand{\Ty}{\mathsf{Ty}}



In this section we show that it is possible to reconstruct the structure
of a (weak) $\omega$-groupoid from the syntactical framework presented
in Section \ref{sec:syntax} in the style of \cite{txa:csl}. To 
this end, let us call a term $a : \Tm~\AgdaBound{A}$ an $n$-cell if
$\AgdaFunction{level}~\AgdaBound{A}~ \AgdaSymbol{\equiv}~ \AgdaBound{n}$, where 

\begin{code}
level                 : ∀ {Γ} → Ty Γ → ℕ
level *               = 0
level (_=h_ {A} _ _)  = suc (level A) 
\end{code}
%
In any $\omega$-category, any $n$-cell $a$ has a  domain (source), $s^n_m\,a$, and
a codomain (target), $t^n_m\,a$, for each $m \le n$. These are, of
course, $(n \textminus m)$-cells. For each pair of $n$-cells such that for some
$m$, $s^n_m a \equiv t^n_m b$, there must exist their composition
${a \circ^n_m b}$ which is an $n$-cell. Composition is (weakly)
associative. Moreover for any $(n \textminus m)$-cell $\AgdaBound{x}$ there
exists an $n$-cell $\mathsf{id}^n_m\,\AgdaBound{x}$ which
behaves like a (weak) identity with respect to $\circ^n_m$.
For the time being we discuss only the construction of cells and omit
the question of coherence. 

For instance, in the simple case of bicategories, each $2$-cell $a$ has a
horizontal source $s^1_1\,a$ and target $t^1_1\,a$, and also a vertical source
$s^2_1\,a$ and target $t^2_1 a$,
which is also the source and target, of the horizontal source and target,
respectively, of $a$. There is horizontal composition of $1$-cells $\circ^1_1$: $x
\to^f y \to^g z$, and also horizontal composition of $2$-cells
$\circ^2_1$, and vertical composition of $2$-cells $\circ^2_2$. There
is a horizontal identity on $a$, $\mathsf{id}^1_1\,a$, and vertical
identity on $a$, $\mathsf{id}^2_1\,a =
\mathsf{id}^2_2\mathsf{id}^1_1\,a$. 

Thus each $\omega$-groupoid construction is defined with respect to a
\emph{level}, $m$, and depth $n \textminus m$ and the structure of
an $\omega$-groupoid is repeated on each level. As we are working purely syntactically we
may make use of this fact and define all groupoid structure only at level
$m=1$ and provide a so-called \emph{replacement operation} which allows us to lift
any cell to an arbitrary type $A$. It is called 'replacement' because
we are syntactically replacing the base type $*$ with an arbitrary
type, $A$.

An important general mechanism we rely on throughout the development
follows directly from the type of the only nontrivial constructor of $\Tm$,
$\mathsf{coh}$, which tells us that to construct a
new term of type $\Gamma \vdash A$, we need a contractible context,
$\Delta$, a type $\Delta\vdash T$ and a context morphism $\delta :
\Gamma \Rightarrow \Delta$ such that
%
\[
\AgdaBound{T} \,\AgdaFunction{[}\, \AgdaBound{δ}\,
\AgdaFunction{]T}~\AgdaDatatype{≡}~\AgdaBound{A}
\]
%
Because in a contractible context all types are inhabited we may in a
way work freely in $\Delta$ and then pull back all terms to $A$ using
$\delta$. 
To show this formally, we must first define identity context morphisms
which complete the definition of a \emph{category} of contexts and
context morphisms:

\begin{code}
IdCm : ∀{Γ} → Γ ⇒ Γ
\end{code}
It satisfies the following property:

\begin{code}
IC-T : ∀{Γ}{A : Ty Γ} → A [ IdCm ]T ≡ A
\end{code}
The definition proceeds by structural recursion and therefore extends
to terms, variables and context morphisms with analogous properties. 
It allows us to define at once:

\begin{code}
Coh-Contr      : ∀{Γ}{A : Ty Γ} → isContr Γ → Tm A
Coh-Contr isC  = coh isC IdCm _ ⟦ sym IC-T ⟫
\end{code}
We use $\AgdaFunction{Coh-Contr}$ as follows: for each kind of cell we
want to define, we construct a minimal contractible context built out
of variables together with a context morphism that populates the
context with terms and a lemma that states an equality
between the substitution and the original type.

\AgdaHide{
\begin{code}
IC-v  : ∀{Γ : Con}{A : Ty Γ}(x : Var A) → x [ IdCm ]V ≅ var x
IC-cm  : ∀{Γ Δ : Con}(δ : Γ ⇒ Δ)        → δ ⊚ IdCm ≡ δ
IC-tm : ∀{Γ : Con}{A : Ty Γ}(a : Tm A) → a [ IdCm ]tm ≅ a

IdCm {ε}       = •
IdCm {Γ , A} = IdCm +S _ , var v0 ⟦ wk+S+T IC-T ⟫

IC-T {Γ} {*} = refl
IC-T {Γ} {a =h b} = hom≡ (IC-tm a) (IC-tm b)

IC-v {.(Γ , A)} {.(A +T A)} (v0 {Γ} {A}) = wk-coh ∾ cohOp (wk+S+T IC-T)
IC-v {.(Γ , B)} {.(A +T B)} (vS {Γ} {A} {B} x) = wk-coh ∾ wk+S+tm (var x) (IC-v _)

IC-cm • = refl
IC-cm (δ , a) = cm-eq (IC-cm δ) (cohOp [⊚]T ∾ IC-tm a) 

IC-tm (var x) = IC-v x
IC-tm (coh x δ A) = cohOp (sym [⊚]T) ∾ coh-eq (IC-cm δ)

pr1 : ∀ {Γ A} → (Γ , A) ⇒ Γ
pr2 : ∀ {Γ A} → Tm {Γ , A} (A [ pr1 ]T)

pr1-wk-T  : ∀{Γ : Con}{A B : Ty Γ} → A [ pr1 ]T ≡ A +T B
pr1-wk-tm : ∀{Γ : Con}{A B : Ty Γ}{a : Tm A} 
          → a [ pr1 ]tm ≅ a +tm B
pr1-wk-cm : ∀{Γ Δ : Con}{A B : Ty Γ}(δ : Γ ⇒ Δ) 
          → δ ⊚ (pr1 {Γ} {B}) ≡ δ +S _

pr2-v0 : ∀ {Γ A} → pr2 {Γ} {A} ≅ var v0

pr-beta : ∀ {Γ A} → (pr1 {Γ} {A} , pr2) ≡ IdCm

pr1 {Γ} = IdCm +S _

pr1-wk-T = wk+S+T IC-T

pr1-wk-tm {a = a} = wk+S+tm a (IC-tm a)

pr1-wk-cm δ = wk+S+S (IC-cm _)

pr2 = var v0 ⟦ wk+S+T IC-T ⟫

pr2-v0 {A = A} = cohOp (trans [+S]T (wk-T IC-T))

pr-beta = refl


data IsId : {Γ Δ : Con}(γ : Γ ⇒ Δ) → Set where
  isId-bsc : {γ : ε ⇒ ε} → IsId γ
  isId-ind : {Γ Δ : Con}{γ : Γ ⇒ Δ} → IsId γ → 
             {A : Ty Γ}{B : Ty Δ} → 
             (eq : B [ γ ]T ≡ A) 
           → IsId {Γ , A} {Δ , B} (γ +S _ , var v0 ⟦ wk+S+T eq ⟫)


IC-IsId : {Γ : Con} → IsId (IdCm {Γ})
IC-IsId {ε} = isId-bsc
IC-IsId {Γ , A} = isId-ind (IC-IsId {Γ}) IC-T


IC-tm'-v0 : {Γ Δ : Con}{A : Ty Γ}{B : Ty Δ}{γ : (Γ , A) ⇒ (Δ , B)} → IsId γ → var v0 [ γ ]tm ≅ var v0
IC-tm'-v0 (isId-ind isd refl) = wk-coh ∾ cohOp (trans [+S]T refl)


Id-with : {Γ : Con}{A : Ty Γ} →
           (x : Tm A) 
         → Γ ⇒ (Γ , A)
Id-with x = IdCm , (x ⟦ IC-T ⟫)


apply-cm'' : {Γ Δ : Con}{A : Ty Γ} →
             (x : Tm A)(γ : Γ ⇒ Δ){B : Ty Δ}(p : B [ γ ]T ≡ A)
          → Γ ⇒ (Δ , B)
apply-cm'' x γ p = γ , (x ⟦ p ⟫)


apply'' : {Γ Δ : Con}{A : Ty Γ}
          (x : Tm A)(γ : Γ ⇒ Δ){B : Ty Δ}
          (p : B [ γ ]T ≡ A){C : Ty (Δ , B)}
          (f : Tm {Δ , B} C)
        → Tm (C [ apply-cm'' x γ p ]T)
apply'' x γ p f = f [ apply-cm'' x γ p ]tm

apply-x : {Γ : Con}{A : Ty Γ} →
          {x : Tm A} 
        → var v0 [ Id-with x ]tm ≅ x
apply-x = wk-coh ∾ (cohOp IC-T)

apply-id : {Γ : Con}{A B : Ty Γ} →
           {x : Tm A}(y : Tm B)
        → (y +tm A) [ Id-with x ]tm ≅ y
apply-id y = (+tm[,]tm y) ∾ (IC-tm _)

apply-T : {Γ : Con}{A : Ty Γ}(B : Ty (Γ , A)) →
          (x : Tm A) 
        → Ty Γ
apply-T B x = B [ Id-with x ]T


apply : {Γ : Con}{A : Ty Γ}{B : Ty (Γ , A)} →
        (f : Tm {Γ , A} B) → 
        (x : Tm A) 
      → Tm (apply-T B x)
apply t x = t [ Id-with x ]tm

apply-2 : {Γ : Con}
          {A : Ty Γ}
          {B : Ty (Γ , A)}
          {C : Ty (Γ , A , B)}
          (f : Tm {Γ , A , B} C)
          (x : Tm A)(y : Tm B)
        → Tm (apply-T (apply-T C y) x)
apply-2 f x y = (f [  Id-with y ]tm) [  Id-with x ]tm

apply-3 : {Γ : Con}
          {A : Ty Γ}
          {B : Ty (Γ , A)}
          {C : Ty (Γ , A , B)}
          {D : Ty (Γ , A , B , C)}
          (f : Tm {Γ , A , B , C} D)
          (x : Tm A)(y : Tm B)(z : Tm C)
         →  Tm (apply-T (apply-T (apply-T D z) y) x)
apply-3 f x y z = ((f [  Id-with z ]tm) [  Id-with y ]tm) [ Id-with x ]tm

fun : {Γ : Con}{A B : Ty Γ} → 
      Tm (B +T A)
    → (Tm {Γ} A → Tm {Γ} B) 
fun t a = (t [ Id-with a ]tm) ⟦ sym (trans +T[,]T IC-T) ⟫


\end{code}

}