
\AgdaHide{
\begin{code}

{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check #-}


module GroupoidStructure where

open import Relation.Binary.PropositionalEquality 
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat


open import BasicSyntax renaming (_∾_ to htrans)
open import IdentityContextMorphisms
open import Suspension

\end{code}
}

\subsection{First-level Groupoid Structure}
We can proceed to the definition of the groupoid structure of the syntax. We start with the base case: 1-cells. Replacement defined above allows us to lift this structure to an arbitrary level $n$ (we leave most of the routine details out). This shows that the syntax is a 1-groupoid on each level. In the next section we show how also the higher-groupoid structure can be defined. 

We start by an essential lemma which formalises the discussion at the
beginning of this section: to construct a term in a type $A$ in an
arbitrary context, we first restrict attention to a suitable
contractible context $\Delta$ and use lifting and substitution -- replacement -- to pull
 the term built by $\AgdaInductiveConstructor{coh}$ in $\Delta$
back. This relies on the fact that a lifted contractible context is
also contractible, and therefore any type lifted from a contractible
context is also inhabited.

\begin{code}
Coh-rpl  : ∀{Γ Δ}(A : Ty Γ)(B : Ty Δ) → isContr Δ
         → Tm (rpl-T A B)
Coh-rpl {_} {Δ} A _ isC = coh (ΣC-it-ε-Contr A isC) _ _
\end{code}
Next we define the reflexivity, symmetry and transitivity terms of any type. Let's start from some base cases. Each of the base cases is derivable in a different contractible context with \AgdaFunction{Coh-Contr} which gives you a coherence constant for any type in any contractible context.

\noindent \textbf{Reflexivity} (identity) It only requires a one-object context.

\begin{code}
refl*-Tm : Tm {x:*} (var v0 =h var v0)
refl*-Tm = Coh-Contr c*
\end{code}
\noindent  \textbf{Symmetry} (inverse) It is defined similarly. Note that the intricate names of contexts, as in \AgdaDatatype{Ty} \AgdaFunction{x:*,y:*,α:x=y} indicate their definitions which have been hidden. Recall that Agda treats all sequences of characters uninterrupted by whitespace as identifiers. For instance \AgdaFunction{x:*,y:*,α:x=y} is a name of a context for which we are assuming the definition:
\AgdaFunction{x:*,y:*,α:x=y} \AgdaSymbol{=} \AgdaInductiveConstructor{ε} \AgdaInductiveConstructor{,} \AgdaInductiveConstructor{*} \AgdaInductiveConstructor{,} \AgdaInductiveConstructor{*} \AgdaInductiveConstructor{,} \AgdaSymbol{(}\AgdaInductiveConstructor{var} \AgdaSymbol{(}\AgdaInductiveConstructor{vS} \AgdaInductiveConstructor{v0}\AgdaSymbol{)} \AgdaInductiveConstructor{=h} \AgdaInductiveConstructor{var} \AgdaInductiveConstructor{v0}\AgdaSymbol{)}.


\begin{code}
sym*-Ty : Ty x:*,y:*,α:x=y
sym*-Ty = vY =h vX

sym*-Tm : Tm {x:*,y:*,α:x=y} sym*-Ty
sym*-Tm = Coh-Contr (ext c* v0)
\end{code}
\textbf{Transitivity} (composition)

\begin{code}
trans*-Ty : Ty x:*,y:*,α:x=y,z:*,β:y=z
trans*-Ty = (vX +tm _ +tm _) =h vZ

trans*-Tm : Tm trans*-Ty
trans*-Tm = Coh-Contr (ext (ext c* v0) (vS v0))
\end{code}
\noindent To obtain these terms for any given type in any give context, we use replacement.

\begin{code}
refl-Tm    : {Γ : Con}(A : Ty Γ) 
           → Tm (rpl-T {Δ = x:*} A (var v0 =h var v0))
refl-Tm A  = rpl-tm A refl*-Tm

sym-Tm : ∀ {Γ}(A : Ty Γ) → Tm (rpl-T A sym*-Ty)
sym-Tm A = rpl-tm A sym*-Tm

trans-Tm : ∀ {Γ}(A : Ty Γ) → Tm (rpl-T A trans*-Ty)
trans-Tm A = rpl-tm A trans*-Tm
\end{code}
\AgdaHide{
\begin{code}

-- The version without lifting function

refl-Tm' :  {Γ : Con}(A : Ty Γ) → Tm {Γ , A} (var v0 =h var v0)
refl-Tm' A = (refl-Tm A)  [ map-1 ]tm ⟦ prf1 ⟫
  where
    prf : rpl-tm {Δ = x:*} A (var v0) [ map-1 ]tm ≅ var v0
    prf = htrans (congtm (htrans ([⊚]tm (Σtm-it A (var v0))) 
          (htrans (congtm (Σtm-it-p1 A)) (htrans wk-coh wk-coh+)))) 
           (1-1cm-same-v0 (ΣT-it-p1 A))

    prf1 : (var v0 =h var v0) ≡ rpl-T {Δ = x:*} A (var v0 =h var v0) [ map-1 ]T
    prf1 = sym (trans (congT (rpl-T-p2 x:* A)) (hom≡ prf prf))

refl-Fun : (Γ : Con)(A : Ty Γ)(x : Tm A) → Tm (x =h x)
refl-Fun Γ A x =  (refl-Tm A) 
                 [ IdCm , x ⟦ rpl*-A ⟫ ]tm 
                 ⟦ sym (trans (congT (rpl-T-p2 x:* A)) (hom≡ (rpl*-a A) (rpl*-a A))) ⟫

Tm-sym-fun : (Γ : Con)(A : Ty Γ) 
       → Tm (rpl-T  {Δ = ε , * , *} A (var (vS v0) =h var v0)) 
       → Tm (rpl-T  {Δ = ε , * , *} A (var v0 =h var (vS v0)))
Tm-sym-fun Γ A = fun (sym-Tm A ⟦ sym (rpl-T-p3 (ε , * , *) A) ⟫)

Tm-sym-fun2 : (Γ : Con)(A : Ty Γ) 
       → Tm {Γ , A , A +T A} (var (vS v0) =h var v0) 
       → Tm {Γ , A , A +T A} (var v0 =h var (vS v0))
Tm-sym-fun2 Γ A t =
  (t [ (wk-id , 
  (var v0 ⟦ eq1 ⟫)) ,
  (var (vS v0) ⟦ eq2 ⟫) ]tm)
  ⟦ sym (trans wk-hom (hom≡ (htrans (cohOp +T[,]T) 
    (cohOp eq1)) 
    (cohOp eq2))) ⟫

  where 
    wk-id : (Γ , A , A +T A) ⇒ Γ 
    wk-id = (IdCm +S A) +S (A +T A)
  
    eq1 : A [ wk-id ]T ≡ (A +T A) +T (A +T A) 
    eq1 = wk+S+T (wk+S+T IC-T)

    eq2 : (A +T A) [ wk-id , (var v0 ⟦ eq1 ⟫) ]T 
            ≡ (A +T A) +T (A +T A) 
    eq2 = trans +T[,]T eq1

Fun-sym : (Γ : Con)(A : Ty Γ)(a b : Tm A) →
          Tm (a =h b)
       → Tm (b =h a)
Fun-sym Γ A a b t = (sym-Tm A) [ rpl-sub Γ A a b t ]tm 
         ⟦ sym (trans (rpl-T-p3-wk (ε , * , *) A) (trans (congT (rpl-T-p2 (ε , * , *) A)) 
           (hom≡ (rpl-tm-v0 (ε , *) A (cohOp (rpl*-A2 A))) (htrans (rpl-tm-vS (ε , *) A)
                 (rpl*-a A))))) ⟫


\end{code}
}
For each of reflexivity, symmetry and transitivity we can construct appropriate coherence 2-cells witnessing the groupoid laws. The base case for variable contexts is proved simply using contractibility as well. However the types of these laws are not as trivial as the proving parts. We use substitution to define the application of the three basic terms we have defined above.

\AgdaHide{
\begin{code}

reflX : Tm (vX =h vX)
reflX = refl-Tm * +tm _ +tm _

reflY : Tm (vY =h vY)
reflY = refl-Tm * +tm _

m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q : Con
m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q = x:*,y:*,α:x=y,z:*,β:y=z , * , (var (vS (vS v0)) =h var v0)

vM : Tm {m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q} *
vM = var (vS (vS (vS (vS (vS (vS v0))))))

vN : Tm {m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q} *
vN = var (vS (vS (vS (vS (vS v0)))))

vMN : Tm {m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q} (vM =h vN)
vMN = var (vS (vS (vS (vS v0))))

vP : Tm {m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q} *
vP = var (vS (vS (vS v0)))

vNP : Tm {m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q} (vN =h vP)
vNP = var (vS (vS v0))

vQ : Tm {m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q} *
vQ = var (vS v0)

vPQ : Tm {m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q} (vP =h vQ)
vPQ = var v0

Ty-G-assoc* : Ty m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q
Ty-G-assoc* = (trans*-Tm [ ((((• , vM) , vP) , 
                       (trans*-Tm [ pr1 ⊚ pr1 ]tm)) , vQ) , vPQ ]tm =h 
             trans*-Tm [ (pr1 ⊚ pr1 ⊚ pr1 ⊚ pr1 , vQ) , 
                       (trans*-Tm [ ((((• , vN) , vP) , vNP) , vQ) , vPQ ]tm) ]tm)

\end{code}
}

\begin{code}
Tm-right-identity* : Tm {x:*,y:*,α:x=y}
         (trans*-Tm [ IdCm , vY , reflY ]tm =h vα)
Tm-right-identity* = Coh-Contr (ext c* v0)

Tm-left-identity* : Tm {x:*,y:*,α:x=y}
         (trans*-Tm [ ((IdCm ⊚ pr1 ⊚ pr1) , vX) ,
          reflX , vY , vα ]tm =h vα)
Tm-left-identity* = Coh-Contr (ext c* v0)

Tm-right-inverse* : Tm {x:*,y:*,α:x=y}
         (trans*-Tm [ (IdCm , vX) , sym*-Tm ]tm =h reflX)
Tm-right-inverse* = Coh-Contr (ext c* v0)



Tm-left-inverse* : Tm {x:*,y:*,α:x=y}
         (trans*-Tm [ ((• , vY) , vX , sym*-Tm , vY) , vα ]tm =h reflY)
Tm-left-inverse* = Coh-Contr (ext c* v0)

Tm-G-assoc* : Tm Ty-G-assoc*
Tm-G-assoc* = Coh-Contr (ext (ext (ext c* v0) (vS v0)) (vS v0))
\end{code}
\noindent Their general versions are defined using replacement. For instance, for associativity, we define:

\begin{code}
Tm-G-assoc    : ∀{Γ}(A : Ty Γ) → Tm (rpl-T A Ty-G-assoc*)
Tm-G-assoc A  = rpl-tm A Tm-G-assoc* 
\end{code}
Following the same pattern, the n-level groupoid laws can be obtained as the coherence constants as well.