
\AgdaHide{
\begin{code}

{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check #-}


module BasicLaws where

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
Coh-Contr : {Γ : Con}{A : Ty Γ} →
             isContr Γ 
           → Tm A
Coh-Contr isC = JJ isC (IdCm _) _ ⟦ sym (IC-T _) ⟫


Coh-rpl : {Γ Δ : Con}(A : Ty Γ)(B : Ty Δ) →
             isContr Δ
           → Tm {rpl Δ A} (rpl-T A B)
Coh-rpl {Γ} {Δ} A B isc = JJ (rep-C-ε-Contr A isc) (rpl-pr2 Δ A) (rep-T A B)


apply-cm : {Γ : Con}{A : Ty Γ} →
           (x : Tm A) 
         → Γ ⇒ (Γ , A)
apply-cm x = (IdCm _) , (x ⟦ IC-T _ ⟫)


apply-cm' : {Γ : Con}{A B : Ty Γ} →
            (x : Tm A)(prf : B ≡ A)
          → Γ ⇒ (Γ , B)
apply-cm' x prf = (IdCm _) , x ⟦ trans (IC-T _) prf ⟫


apply-x : {Γ : Con}{A : Ty Γ} →
          {x : Tm A} 
        → var v0 [ apply-cm x ]tm ≅ x
apply-x = htrans wk-coh (cohOp (IC-T _))


apply-x' : {Γ : Con}{A B : Ty Γ} →
          {x : Tm A}{prf : B ≡ A}
        → var v0 [ apply-cm' x prf ]tm ≅ x
apply-x' = htrans wk-coh (cohOp (trans (IC-T _) _))


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

fun : {Γ : Con}{A B : Ty Γ} → 
      Tm (B +T A)
    → (Tm {Γ} A → Tm {Γ} B) 
fun t a = (t [ apply-cm a ]tm) ⟦ sym (trans +T[,]T (IC-T _)) ⟫


\end{code}

To show the syntax framework is a valid internal language of \wog{}, as a first step, we should produce a reflexivity term for the equality of any type.

We use a context with a type to denote the non-empty context.


We tried several ways to get the reflexivity terms. One of them is to define the suspension of contexts first and then suspend a term of the base type n times to get the n-cell reflexivity.

\begin{code}


refl*-Con : Con
refl*-Con = ε , *

refl* :  Tm {ε , *} (var v0 =h var v0)
refl* = Coh-Contr c*


Tm-refl' :  (Γ : Con)(A : Ty Γ) → Tm (rpl-T {Δ = ε , *} A (var v0 =h var v0))
Tm-refl' Γ A = rpl-tm A refl*


\end{code}

\AgdaHide{
\begin{code}

Tm-refl :  (Γ : Con)(A : Ty Γ) → Tm {Γ , A} (var v0 =h var v0)
Tm-refl Γ A = (Tm-refl' Γ A)  [ map-1 ]tm ⟦ prf1 ⟫
  where
    prf : rpl-tm {Δ = ε , *} A (var v0) [ map-1 ]tm ≅ var v0
    prf = htrans (congtm (htrans ([⊚]tm (rep-tm A (var v0))) 
          (htrans (congtm (rep-tm-p1 A)) (htrans wk-coh wk-coh+)))) 
           (1-1cm-same-v0 (rep-T-p1 A))

    prf1 : (var v0 =h var v0) ≡ rpl-T {Δ = ε , *} A (var v0 =h var v0) [ map-1 ]T
    prf1 = sym (trans (congT (rpl-T-p2 (ε , *) A)) (hom≡ prf prf))

{-
tsp-Tm base-1 T-eq (Tm-refl' Γ A)
  where
    t-eq : rpl-tm (ε , *) A (var v0) [  IdCm' base-1 ]tm ≅ var v0
    t-eq = htrans (congtm (rpl-tm-v0' ε A)) (IC-tm'-v0 base-1)

    T-eq :  (rpl-T (ε , *) A (var v0 =h var v0))  [ IdCm' base-1 ]T ≡ (var v0 =h var v0)
    T-eq = trans (congT (rpl-T-p2 (ε , *) A)) (hom≡ t-eq t-eq)

-}
\end{code}
}

The one above is special for the reflexivity of the last variable in a non-empty context. We also define a more general version which is the reflexivity for any term of any type in given context. 

\begin{code}

Fun-refl : (Γ : Con)(A : Ty Γ)(x : Tm A) → Tm (x =h x)
Fun-refl Γ A x =  (Tm-refl' Γ A) 
                 [ apply-cm' x (rep-T-p1 _) ]tm 
                 ⟦ sym (trans (congT (rpl-T-p2 (ε , *) A)) (hom≡ (rpl*-a A) (rpl*-a A))) ⟫

\end{code}

We also construct the symmetry for the morphism between the last two variables.


\begin{code}

sym*-Con : Con
sym*-Con = refl*-Con , * , (var (vS v0) =h var v0)

Tm-sym* : Tm {sym*-Con} (((var v0) =h (var (vS v0))) +T _)
Tm-sym* = Coh-Contr (ext c* v0)

Tm-sym : (Γ : Con)(A : Ty Γ)
        → Tm (rpl-T  {Δ = sym*-Con} A (((var v0) =h (var (vS v0))) +T _))
Tm-sym Γ A = rpl-tm A Tm-sym*

\end{code}

\AgdaHide{
\begin{code}
Tm-sym-fun : (Γ : Con)(A : Ty Γ) 
       → Tm (rpl-T  {Δ = ε , * , *} A (var (vS v0) =h var v0)) 
       → Tm (rpl-T  {Δ = ε , * , *} A (var v0 =h var (vS v0)))
Tm-sym-fun Γ A = fun (Tm-sym Γ A ⟦ sym (rpl-T-p3 (ε , * , *) A) ⟫)

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


Fun-sym : (Γ : Con)(A : Ty Γ)(a b : Tm A) →
          Tm (a =h b)
       → Tm (b =h a)
Fun-sym Γ A a b t = (Tm-sym Γ A) [ rpl-sub Γ A a b t ]tm 
         ⟦ sym (trans (rpl-T-p3-wk (ε , * , *) A) (trans (congT (rpl-T-p2 (ε , * , *) A)) 
           (hom≡ (rpl-tm-v0 (ε , *) A (rpl*-A2 A)) (htrans (rpl-tm-vS (ε , *) A)
                 (rpl*-a A))))) ⟫

\end{code}
}

Then the transitivity for three consecutive variables at the last of a context is as follows.

\begin{code}

trans*-Con : Con
trans*-Con = sym*-Con , * , (var (vS (vS v0)) =h var v0)

trans*-Ty : Ty trans*-Con
trans*-Ty = (var (vS (vS (vS v0))) =h var v0) +T _

trans*-Tm : Tm trans*-Ty
trans*-Tm = Coh-Contr (ext (ext c* v0) (vS v0))

Tm-trans' : {Γ : Con}(A : Ty Γ) → Tm (rpl-T A trans*-Ty)
Tm-trans' A = rpl-tm A trans*-Tm

\end{code}



\AgdaHide{

\begin{code}



-- rpl-T trans*-Con A trans*-Ty ≡ (rpl-T (ε , * , * , (var (vS v0) =h var v0) , *) A (var (vS (vS (vS v0))) =h var v0)) +T _


{-
transCon : {Γ : Con}(A : Ty Γ) → Con
transCon {Γ} A = (Γ , A , A +T A , (A +T A) +T (A +T A))

Fun-trans : (Γ : Con)(A : Ty Γ) 
         → Tm {transCon A} (var (vS (vS v0)) =h var (vS v0))
         → Tm {transCon A} (var (vS v0) =h var v0) 
         → Tm {transCon A} (var (vS (vS v0)) =h var v0)
Fun-trans Γ A p q = 
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
-}

{-
Tm-trans : (Γ : Con)(A : Ty Γ)(x y z : Tm A)(p : Tm (x =h y))(q : Tm (y =h z))
         → Tm (x =h z)
Tm-trans Γ A x y z p q = Tm-trans' A 
                         [ (((IdCm _) , x ⟦ rpl*-A ⟫) , y ⟦ rpl*-A2 A ⟫) , p ⟦ rpl-xy A x y ⟫ , 
                           {!z!} , {!!} ]tm 
                         ⟦ {!!} ⟫
-}

{-
z ⟦ trans (rpl-T-p3-wk (ε , * , *) A) (trans (rpl-T-p3-wk (ε , *) A) (rpl*-A2 A)) ⟫ 
                         , q ⟦ trans (congT (rpl-T-p2 (ε , * , * , (var (vS v0) =h var v0) , *) A)) 
                               (hom≡ (htrans (rpl-tm-vS (ε , * , * , (var (vS v0) =h var v0)) A) (htrans (rpl-tm-vS (ε , * , *) A) (rpl-tm-v0 (ε , *) A (rpl*-A2 A)))) (rpl-tm-v0 (ε , * , * , (var (vS v0) =h var v0)) A (trans (rpl-T-p3-wk (ε , * , *) A) (trans (rpl-T-p3-wk (ε , *) A) (rpl*-A2 A))) )) ⟫

-}
-- sym (trans (congT (trans (rpl-T-p3 (ε , * , * , (var (vS v0) =h var v0) , *) A) ?)) {!!})


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