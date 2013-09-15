
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


We tried several ways to get the reflexivity terms. One of them is to define the suspension of contexts first and then suspend a term of the base type n times to get the n-cell reflexivity. The encoding of the suspension is finished and will be showed later, however we found that there is a simpler way to do it.




\paragraph{Loop Context}

Here we are going to use some special contexts which are called \emph{loop context} in this paper. For any type in any context, we could always filter out the unrelated part to get a minimum context for this type which is a loop context. 

A loop context is either a singleton context with only one variable of the base set, or it is inductively defined by adding a new variable of the same type as the last variable from a loop context and a morphism between these two variables. We will use a function to show what is a loop context.

\begin{code}
{-
ΩCon : ℕ → Con*
ΩCon 0 = ε ,, *
ΩCon (suc n) = let (Γ ,, A) = ΩCon n in
                   (Γ , A , A +T A) ,, (var (vS v0) =h var v0)
-}

\end{code}

A variable of the base type is a 0-cell, and the morphism between any two n-cells is an $n+1$-cell as mentioned before. A level-n loop context is the minimum non-empty context where the last variable is n-cell. We could easily prove such a context is contractible. Intuitively it is a special kind of contractible context where the branching approach is unique as we always create an $n+1$ cell for level-n loop context to get a level-(n+1) loop context. Since a loop context is contractible, all types are inhabited.  The approach to get the reflexivity is to use J-term with a corresponding loop context. The idea is easy but there are three difficult steps.


\AgdaHide{
\begin{code}

-- calculate level of Type A

tylevel : {Γ : Con}(A : Ty Γ) → ℕ
tylevel * = 0
tylevel (_=h_ {A} a b) = suc (tylevel A)


{-
loopΩ-count : Con* → Con*
loopΩ-count (_ ,, A) = ΩCon (tylevel A)
-}

\end{code}
}

First we need to define a function called $loop\Omega$ to get the required loop context. $loop\Omega'$ is the complete version which returns five different things, the previous context, the last type, a context morphism between the input previous context and output previous context, a proof term that substitute the output last type with the context morphism is equal to the input last type and another proof term that it is a contractible context. It is necessary to combine them together, because it will become much more involved if they are defined separately.

\AgdaHide{
\begin{code}

{-
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

-}
\end{code}
}

\AgdaHide{
\begin{code}
{-
loopΩ-Contr : (ne : Con*) → isContr ∥ loopΩ ne ∥
loopΩ-Contr (Γ ,, A) with (loopΩ' Γ A)
... |  (Γ' ,, A' ,, γ' ,, prf' ,, isc) = isc


loopΩ-refl : (ne : Con*) → Reflexive (loopΩ ne)
loopΩ-refl ne = anyTypeInh (loopΩ-Contr ne)
-}

Reflexive : (Γ : Con)(A : Ty Γ) → Set
Reflexive Γ A = Tm {Γ , A} (var v0 =h var v0)

refl* : Reflexive ε *
refl* = anyTypeInh c*

\end{code}
}

The second problem is to define the context morphism, namely the substitution between the orignal context and the corresponding loop context. And the third problem is to prove type unification for the J-terms. The auxiliary functions make the proofs look much simpler that it was earlier. rep-T-p1

\begin{code}

Tm-refl'' :  (Γ : Con)(A : Ty Γ) → Tm (rpl-T  (ε , *) A (var v0 =h var v0))
Tm-refl'' Γ A = rpl-tm (ε , *) A refl*

Tm-refl' :  (Γ : Con)(A : Ty Γ) → Reflexive Γ A
Tm-refl' Γ A = (Tm-refl'' Γ A)  [ δ ]tm ⟦ prf1 ⟫
  where
    δ : (Γ , A) ⇒ rpl (ε , *) A
    δ = 1-1cm-same (rep-T-p1 A)

    prf : rpl-tm (ε , *) A (var v0) [ δ ]tm ≅ var v0
    prf = htrans (congtm (htrans ([⊚]tm (rep-tm A (var v0))) (htrans (congtm (rep-tm-p1 A)) (htrans wk-coh wk-coh+)))) 
           (1-1cm-same-v0 (rep-T-p1 A))

    prf1 : (var v0 =h var v0) ≡ rpl-T (ε , *) A (var v0 =h var v0) [ δ ]T
    prf1 = sym (trans (congT (rpl-T-p2 (ε , *) A)) (hom≡ prf prf))

\end{code}

The one above is special for the reflexivity of the last variable in a non-empty context. We also define a more general version which is the reflexivity for any term of any type in given context. 


\begin{code}

apply-cm : {Γ : Con}{A : Ty Γ} →
           (x : Tm A) 
         → Γ ⇒ (Γ , A)
apply-cm x = (IdCm _) , (x ⟦ IC-T _ ⟫)


apply-x : {Γ : Con}{A : Ty Γ} →
          {x : Tm A} 
        → var v0 [ apply-cm x ]tm ≅ x
apply-x = htrans wk-coh (cohOp (IC-T _))

apply-id : {Γ : Con}{A B : Ty Γ} →
           {x : Tm A}(y : Tm B)
        → (y +tm A) [ apply-cm x ]tm ≅ y
apply-id y = htrans (+tm[,]tm y) (IC-tm _)

apply-T : {Γ : Con}{A : Ty Γ}(B : Ty (Γ , A)) →
          (x : Tm A) 
        → Ty Γ
apply-T B x = B [ apply-cm x ]T


apply : {Γ : Con}{A : Ty Γ}{B : Ty (Γ , A)} →
        (f : Tm {Γ , A} B) → 
        (x : Tm A) 
      → Tm (apply-T B x)
apply t x = t [ apply-cm x ]tm


apply-2 : {Γ : Con}
          {A : Ty Γ}
          {B : Ty (Γ , A)}
          {C : Ty (Γ , A , B)}
          (f : Tm {Γ , A , B} C)
          (x : Tm A)(y : Tm B)
        → Tm (apply-T (apply-T C y) x)
apply-2 f x y = (f [ apply-cm y ]tm) [ apply-cm x ]tm

apply-3 : {Γ : Con}
          {A : Ty Γ}
          {B : Ty (Γ , A)}
          {C : Ty (Γ , A , B)}
          {D : Ty (Γ , A , B , C)}
          (f : Tm {Γ , A , B , C} D)
          (x : Tm A)(y : Tm B)(z : Tm C)
         →  Tm (apply-T (apply-T (apply-T D z) y) x)
apply-3 f x y z = ((f [ apply-cm z ]tm) [ apply-cm y ]tm) [ apply-cm x ]tm

{-
abs : {Γ : Con}{A B : Ty Γ} → 
           (Tm {Γ} A → Tm {Γ} B) 
         → Tm {Γ , A} (B +T A)
abs f = var v0 ⟦ {!!} ⟫
-}

-- interpret abs

fun : {Γ : Con}{A B : Ty Γ} → 
      Tm (B +T A)
    → (Tm {Γ} A → Tm {Γ} B) 
fun t a = (t [ apply-cm a ]tm) ⟦ sym (trans +T[,]T (IC-T _)) ⟫


Tm-refl : (Γ : Con)(A : Ty Γ)(x : Tm A) → Tm (x =h x)
Tm-refl Γ A x = apply (Tm-refl' Γ A) x ⟦ sym (hom≡ apply-x apply-x) ⟫ 

\end{code}

We also construct the symmetry for the morphism between the last two variables.

\begin{code}


Tm-sym* : Tm {ε , * , * , _} (((var v0) =h (var (vS v0))) +T _)
Tm-sym* = anyTypeInh (ext c* v0)

Tm-sym' : (Γ : Con)(A : Ty Γ)
        → Tm (rpl-T  (ε , * , * , _) A (((var v0) =h (var (vS v0))) +T _))
Tm-sym' Γ A = rpl-tm (ε , * , * , _) A Tm-sym*

Tm-sym-fun : (Γ : Con)(A : Ty Γ) 
       → Tm (rpl-T  (ε , * , *) A (var (vS v0) =h var v0)) 
       → Tm (rpl-T  (ε , * , *) A (var v0 =h var (vS v0)))
Tm-sym-fun Γ A = fun (Tm-sym' Γ A ⟦ sym (rpl-T-p3 (ε , * , *) A) ⟫)

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
    wk-id = (IdCm Γ +S A) +S (A +T A)
  
    eq1 : A [ wk-id ]T ≡ (A +T A) +T (A +T A) 
    eq1 = wk+S+T (wk+S+T (IC-T _))

    eq2 : (A +T A) [ wk-id , (var v0 ⟦ eq1 ⟫) ]T 
            ≡ (A +T A) +T (A +T A) 
    eq2 = trans +T[,]T eq1


Tm-sym : (Γ : Con)(A : Ty Γ)(a b : Tm A) →
          Tm (a =h b)
       → Tm (b =h a)
Tm-sym Γ A a b t = (Tm-sym' Γ A) [ (((IdCm _) , (a ⟦ prf1 ⟫)) , (b ⟦ prf2 ⟫)) , 
                     t ⟦ prf3 ⟫ ]tm 
                 ⟦ sym (trans (congT (rpl-T-p3 {Γ} (ε , * , *) A {var (vS v0) =h var v0}
                                        {var v0 =h var (vS v0)})) (trans +T[,]T 
                 (trans (congT (rpl-T-p2 (ε , * , *) A)) 
                      (hom≡ (rpl-tm-p1 (ε , *) A prf2 b) (htrans (rpl-tm-p2 (ε , *) A prf2 v0) (rpl-tm-p1 ε A prf1 a)))))) ⟫

  where
    prf1 : (rep-T A * [ rpl-pr2 ε A ]T) [ IdCm Γ ]T ≡ A
    prf1 = trans (IC-T _) (rep-T-p1 A)

    prf2 : (rep-T A * [ rpl-pr2 (ε , *) A ]T) [ IdCm Γ , a ⟦ prf1 ⟫ ]T ≡ A
    prf2 = trans (congT (rpl-T-p3 ε A)) (trans +T[,]T prf1)

    prf3 :  (rep-T A (var (vS v0) =h var v0) [ rpl-pr2 (ε , * , *) A ]T) [
              IdCm Γ , a ⟦ prf1 ⟫ , b ⟦ prf2 ⟫ ]T
              ≡ (a =h b)
    prf3 = trans (congT (rpl-T-p2 (ε , * , *) A)) 
                     (hom≡ (htrans (rpl-tm-p2 (ε , *) A prf2 v0) (rpl-tm-p1 ε A prf1 a)) (rpl-tm-p1 (ε , *) A prf2 b))


\end{code}

Then the transitivity for three consecutive variables at the last of a context is as follows.

\begin{code}

transCon : {Γ : Con}(A : Ty Γ) → Con
transCon {Γ} A = (Γ , A , A +T A , (A +T A) +T (A +T A))

Tm-trans-semantic : (Γ : Con)(A : Ty Γ) 
         → Tm {transCon A} (var (vS (vS v0)) =h var (vS v0))
         → Tm {transCon A} (var (vS v0) =h var v0) 
         → Tm {transCon A} (var (vS (vS v0)) =h var v0)
Tm-trans-semantic Γ A p q = 
  (q [ (( wk-id , 
          var (vS (vS v0)) ⟦ eq1 ⟫) , 
          var (vS (vS v0)) ⟦ eq2 ⟫) , 
          var v0 ⟦ trans +T[,]T eq2 ⟫ ]tm) 
   ⟦ sym (trans wk-hom (hom≡ (htrans wk-coh (cohOp eq2)) 
   (cohOp (trans +T[,]T eq2)))) ⟫

  where
    wk-id : transCon A ⇒ Γ
    wk-id = ((IdCm _ +S A) +S (A +T A)) +S ((A +T A) +T (A +T A))

    wk-ty : Ty (transCon A)
    wk-ty = ((A +T A) +T (A +T A)) +T ((A +T A) +T (A +T A))

    eq1 : A [ wk-id ]T ≡ wk-ty
    eq1 = wk+S+T (wk+S+T (wk+S+T (IC-T _)))

    wk-id2 : transCon A ⇒ (Γ , A)
    wk-id2 = (IdCm _ +S (A +T A)) +S ((A +T A) +T (A +T A))

    eq2 : (A +T A) [ wk-id , (var (vS (vS v0)) ⟦ eq1 ⟫) ]T ≡ wk-ty
    eq2 = trans +T[,]T eq1 

\end{code}



\AgdaHide{

\begin{code}

trans-Con : Con
trans-Con = ε , * , * , (var (vS v0) =h var v0) , * , (var (vS (vS v0)) =h var v0)

trans-Con' : {Γ : Con}(A : Ty Γ) → Con
trans-Con' A = rpl trans-Con A

trans-Ty : Ty trans-Con
trans-Ty = (var (vS (vS (vS v0))) =h var v0) +T _

trans-Ty' : {Γ : Con}(A : Ty Γ) → Ty (trans-Con' A)
trans-Ty' A = rpl-T trans-Con A trans-Ty

Tm-trans* : Tm trans-Ty
Tm-trans* = anyTypeInh (ext (ext c* v0) (vS v0))

Tm-trans' : {Γ : Con}(A : Ty Γ) → Tm (trans-Ty' A)
Tm-trans' A = rpl-tm trans-Con A Tm-trans*

Tm-trans : (Γ : Con)(A : Ty Γ) 
         → Tm (rep-T A trans-Ty)
Tm-trans Γ A = rep-tm A Tm-trans*

{-
interpret-eq : {Γ : Con}(A : Ty Γ)(a b : Tm A)(p : Tm (a =h b)) → a ≅ b
interpret-eq A a b p t= {!!}

Tm-J : {Γ : Con}(A : Ty Γ)(P : Ty (Γ , A , A +T A , (var (vS v0) =h var v0))) →
       Tm {Γ , A} (P [ ((IdCm _) ,  (var v0 ⟦ trans +T[,]T (wk+S+T (IC-T _)) ⟫)) , 
             Tm-refl' (Γ ,, A) ⟦ hom≡ (htrans wk-coh (htrans wk-coh (cohOp (trans [+S]T (wk-T (IC-T A)))))) (htrans wk-coh 
                                                     (cohOp (trans +T[,]T (trans [+S]T (wk-T (IC-T A)))))) ⟫ ]T)
     → (a b : Tm A)(p : Tm (a =h b)) 
     → Tm {Γ} (P [ (((IdCm _) , a ⟦ IC-T _ ⟫) , wk-tm (b ⟦ IC-T _ ⟫)) , p ⟦ hom≡ (htrans wk-coh (htrans wk-coh (cohOp (IC-T A)))) (htrans wk-coh (htrans wk-coh (cohOp (IC-T A)))) ⟫ ]T)
Tm-J A P prefl a b p = (prefl [ (IdCm _) , (a ⟦ IC-T _ ⟫) ]tm) ⟦ trans (congT2 (cm-eq (cm-eq (cm-eq 
                 (sym (trans (⊚wk (IdCm _)) (IC-⊚ _))) 
                 ((htrans (cohOp [⊚]T) (htrans (congtm (cohOp (trans [+S]T (wk-T (IC-T A))))) wk-coh)) -¹)) 
                 (htrans wk-coh (htrans (cohOp (IC-T A)) (htrans
                                                            (cohOp
                                                             {a =
                                                              (var v0 ⟦ trans +T[,]T (wk+S+T (IC-T A)) ⟫) [ IdCm _ , a ⟦ IC-T A ⟫
                                                              ]tm}
                                                             [⊚]T)
                                                            (htrans
                                                               (congtm (cohOp (trans +T[,]T (trans [+S]T (wk-T (IC-T A)))))) (htrans wk-coh (htrans (cohOp (IC-T A)) {!p!}))) -¹)))) 
                 {!!})) [⊚]T ⟫

-}

-- htrans (cohOp [⊚]T) (htrans (congtm (cohOp ( trans +T[,]T (trans [+S]T (wk-T (IC-T A)))))) ?)
{-

Tm-trans'' : (Γ : Con)(A : Ty Γ) 
         → Tm {trans-Con' Γ A} (trans-Ty' Γ A)
Tm-trans'' Γ A = JJ (ext (ext c* v0) (vS v0)) {!!} trans-Ty ⟦ {!!} ⟫


ind : {Γ : Con}(A : Ty Γ) → (D : (x y : Tm A)(p : Tm (x =h y)) → Con)
      → ((a : Tm A) → (Σ[ B ∶ Ty (D a a (Tm-refl Γ A a)) ] Tm B))
      → (x y : Tm A)(p : Tm (x =h y)) → Σ[ C ∶ Ty (D x y p) ] Tm C
ind A D dref x y p  with dref x
... | er = {!!} ,, {!!}



transport : {Γ : Con}(A : Ty Γ)(P : Tm A → Con)
            → (a b : Tm A)(p : Tm (a =h b))
            → (P a) ⇒ (P b)
transport A P a b p = {!IdCm (P b) ⊚ ?!}

Tm-J : {Γ : Con}(A : Ty Γ)(P : Ty (Γ , A , A +T A , (var (vS v0) =h var v0)))
     → (a b : Tm A)(p : Tm (a =h b))
     → Tm P → Tm P
Tm-J = {!!}

Tm-trans2 : {Γ : Con}(A : Ty Γ)(a b c : Tm A)
            (p : Tm (a =h b))(q : Tm (b =h c))
          → Tm (a =h c)
Tm-trans2 A a b c p q = {!p [ ? ] ⟦ ? ⟫!}
-}

-- Eckmann-Hilton

-- (Γ : Con)(A : Ty Γ)(x : Tm A)(p q : Tm ((Tm-refl x) =h (Tm-refl x))) → Tm-trans p q ≡ Tm-trans q p


-- EH : (Γ : Con)(A : Ty Γ)

\end{code}
}

There are still a lot of coherence laws to prove but it is going to be very sophisticated. We also tried to construct the J-eliminator for equality in this syntactic approach but have not found a solution. To construct more of them, Altenkirch suggests to use a polymorphism theorem which says that given any types, terms and context morphisms, we could replace the base type $*$ in the context of the objects by some type in another context. With this theorem, any lemmas or term inhabited in contractible context should also be inhabited in higher dimensions. 