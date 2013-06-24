
\AgdaHide{
\begin{code}

{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check #-}


module GroupoidLaws where

open import Relation.Binary.PropositionalEquality 
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat


open import AIOOG renaming (_∾_ to htrans)
open import AIOOGS2
open import Suspension

\end{code}
}

One of the most important feature of the contractible contexts is that any type in a contractible context is inhabited. It can be simply proved by using J-term and identity morphism.

\begin{code}
anyTypeInh : ∀{Γ} → {A : Ty Γ} → isContr Γ → Tm {Γ} A
anyTypeInh {A = A} ctr = JJ ctr (IdCm _)  A ⟦ sym (IC-T _) ⟫
\end{code}

To show the syntax framework is a valid internal language of \wog{}, as a first step, we should produce a reflexivity term for the equality of any type.

We use a context with a type to denote the non-empty context.

\begin{code}
Con* = Σ Con Ty

preCon : Con* → Con
preCon = proj₁

∥_∥ : Con* → Con
∥_∥ = uncurry _,_

lastTy : (Γ : Con*) → Ty (preCon Γ)
lastTy  = proj₂

lastTy' : (Γ : Con*) → Ty ∥ Γ ∥
lastTy' (_ ,, A) = A +T A
\end{code}

\AgdaHide{
\begin{code}

cohOp-hom : {Γ : Con}{A B : Ty Γ}{a b : Tm B}(p : A ≡ B) → (a ⟦ p ⟫ =h b ⟦ p ⟫) ≡ (a =h b)
cohOp-hom refl = refl

\end{code}
}

We tried several ways to get the reflexivity terms. One of them is to define the suspension of contexts first and then suspend a term of the base type n times to get the n-cell reflexivity. The encoding of the suspension is finished and will be showed later, however we found that there is a simpler way to do it.




\paragraph{Loop Context}

Here we are going to use some special contexts which are called \emph{loop context} in this paper. For any type in any context, we could always filter out the unrelated part to get a minimum context for this type which is a loop context. 

We will use a function to show what is a loop context.

\begin{code}
ΩCon : ℕ → Con*
ΩCon 0 = ε ,, *
ΩCon (suc n) = let (Γ ,, A) = ΩCon n in
                   (Γ , A , A +T A) ,, (var (vS v0) =h var v0)
\end{code}

A variable of the base type is a 0-cell, and the morphism between any two n-cells is an $n+1$-cell as mentioned before. A level-n loop context is the minimum non-empty context where the last variable is n-cell. We could easily prove such a context is contractible. Intuitively it is a special kind of contractible context where the branching approach is unique as we always create an $n+1$ cell for level-n loop context to get a level-(n+1) loop context. Since a loop context is contractible, all types are inhabited.  The approach to get the reflexivity is to use J-term with a corresponding loop context. The idea is easy but there are three difficult steps.


\AgdaHide{
\begin{code}

-- calculate level of Type A

tylevel : {Γ : Con}(A : Ty Γ) → ℕ
tylevel * = 0
tylevel (_=h_ {A} a b) = suc (tylevel A)


loopΩ-count : Con* → Con*
loopΩ-count (_ ,, A) = ΩCon (tylevel A)

\end{code}
}

First we need to define a function called $loop\Omega$ to get the required loop context. $loop\Omega'$ is the complete version which returns five different things, the previous context, the last type, a context morphism between the input previous context and output previous context, a proof term that substitute the output last type with the context morphism is equal to the input last type and another proof term that it is a contractible context. It is necessary to combine them together, because it will become much more involved if they are defined separately.

\begin{code}
loopΩ' : (Γ : Con)(A : Ty Γ) 
       → Σ[ Ω ∶ Con ] Σ[ ω ∶ Ty Ω ] Σ[ γ ∶ Γ ⇒ Ω ] 
         Σ[ prf ∶ ω [ γ ]T ≡ A ] isContr (Ω , ω)
loopΩ' Γ * = ε  ,, * ,, • ,, refl ,, c*
loopΩ' Γ (_=h_ {A} a b) with loopΩ' Γ A 
... | (Γ' ,, A' ,, γ' ,, prf' ,, isc) = 
          Γ' , A' , A' +T A' ,,
          (var (vS v0) =h var v0) ,, 
          γ' , (a ⟦ prf' ⟫) , wk-tm (b ⟦ prf' ⟫) ,, 
          (trans wk-hom (trans wk-hom (cohOp-hom prf'))) ,,
          ext isc v0

loopΩ : Con* → Con*
loopΩ (Γ ,, A) with (loopΩ' Γ A)
... |  (Γ' ,, A' ,, γ' ,, prf' ,, isc) = Γ' ,, A'
\end{code}


\AgdaHide{
\begin{code}

loopΩ-Contr : (ne : Con*) → isContr ∥ loopΩ ne ∥
loopΩ-Contr (Γ ,, A) with (loopΩ' Γ A)
... |  (Γ' ,, A' ,, γ' ,, prf' ,, isc) = isc



Reflexive : Con* → Set
Reflexive Γ = Tm {∥ Γ ∥} (var v0 =h var v0)

refl* : Reflexive (ε ,, *)
refl* = anyTypeInh c* -- this decides the type!!!

loopΩ-refl : (ne : Con*) → Reflexive (loopΩ ne)
loopΩ-refl ne = anyTypeInh (loopΩ-Contr ne)

transCon : Con
transCon = ε , * , * , (var (vS v0) =h var v0) , * , (var (vS (vS v0)) =h  var v0)


\end{code}
}

The second problem is to define the context morphism, namely the substitution between the orignal context and the corresponding loop context. And the third problem is to prove type unification for the J-terms. The auxiliary functions make the proofs look much simpler that it was earlier. 

\begin{code}
Tm-refl :  (ne : Con*) → Tm {∥ ne ∥} (var v0 =h var v0)
Tm-refl (Γ ,, A) with loopΩ' Γ A
... | ΩΓ ,, ΩA ,, γ ,, prf ,, isc = 
      JJ isc (γ +S A , wk-tm+ A (var v0 ⟦ wk-T prf ⟫)) (var v0 =h var v0) 
      ⟦ sym (trans wk-hom (trans wk-hom+ (hom≡ (cohOp (wk-T prf))
      (cohOp (wk-T prf))))) ⟫

\end{code}

The one above is special for the reflexivity of the last variable in a non-empty context. We also define a more general version which is the reflexivity for any term of any type in given context. In addition we also obtain the symmetry for the morphism between the last two variables.


\begin{code}
Tm-refl' : (Γ : Con)(A : Ty Γ)(x : Tm A) → Tm (x =h x)
Tm-refl' Γ A x = 
         (Tm-refl (Γ ,, A) [ (IdCm _) , (x ⟦ IC-T A ⟫) ]tm) 
         ⟦ sym (trans wk-hom (hom≡ (cohOp (IC-T A)) (cohOp (IC-T A)))) ⟫


Tm-sym : (Γ : Con)(A : Ty Γ) 
         → Tm {Γ , A , A +T A} (var (vS v0) =h var v0) 
         → Tm {Γ , A , A +T A} (var v0 =h var (vS v0))
Tm-sym Γ A t = (t [ (((IdCm _ +S A) +S (A +T A)) , 
  (var v0 ⟦ trans [+S]T (wk-T (trans [+S]T (wk-T (IC-T _)))) ⟫)) ,
  (var (vS v0) ⟦ trans +T[,]T 
       (trans [+S]T (wk-T (trans [+S]T (wk-T (IC-T _))))) ⟫) ]tm)
  ⟦ sym (trans wk-hom (hom≡ (htrans (cohOp +T[,]T) 
    (cohOp (trans [+S]T (wk-T (trans [+S]T (wk-T (IC-T A))))))) 
    (cohOp (trans +T[,]T (trans [+S]T (wk-T 
      (trans [+S]T (wk-T (IC-T A))))))))) ⟫

\end{code}



\AgdaHide{

\begin{code}

-- replace * with A, repeat same contruction in higher dimension

rep-C : {Γ : Con}(A : Ty Γ) → Con → Con

rep-T : {Γ Δ : Con}(A : Ty Γ) → Ty Δ → Ty (rep-C A Δ)

rep-tm : {Γ Δ : Con}(A : Ty Γ)(B : Ty Δ) → Tm B → Tm (rep-T A B)

rep-cm : {Γ Δ Θ : Con}(A : Ty Γ) → Θ ⇒ Δ → (rep-C A Θ) ⇒ (rep-C A Δ)


rep-C * C = C
rep-C (_=h_ {A} a b) C = ΣC (rep-C A C)

rep-T * B = B
rep-T (_=h_ {A} a b) B = ΣT (rep-T A B)
  
rep-tm * B t = t
rep-tm (_=h_ {A} a b) B t = Σtm _ (rep-tm A B t)


rep-cm * cm = cm
rep-cm (_=h_ {A} a b) cm = Σs (rep-cm A cm)


trans-Con : Con
trans-Con = ε , * , * , (var (vS v0) =h var v0) , * , (var (vS (vS v0)) =h var v0)

trans-Ty : Ty trans-Con
trans-Ty = (var (vS (vS (vS (vS v0)))) =h var (vS v0))

Tm-trans* : Tm trans-Ty
Tm-trans* = JJ (ext (ext c* v0) (vS v0)) (IdCm _) trans-Ty

Tm-trans : (Γ : Con)(A : Ty Γ) 
         → Tm (rep-T A trans-Ty)
Tm-trans Γ A = rep-tm A _ Tm-trans*

\end{code}
}

There are still a lot of coherence laws to prove but it is going to be very sophisticated. We also tried to construct the J-eliminator for equality in this syntactic approach but have not found a solution. To construct more of them, Altenkirch suggests to use a polymorphism theorem which says that given any types, terms and context morphisms, we could replace the base type $*$ in the context of the objects by some type in another context. With this theorem, any lemmas or term inhabited in contractible context should also be inhabited in higher dimensions. 