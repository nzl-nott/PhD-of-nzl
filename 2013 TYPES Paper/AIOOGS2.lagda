
\AgdaHide{
\begin{code}
module AIOOGS2 where


open import AIOOG
open import Relation.Binary.PropositionalEquality 
open import Data.Product renaming (_,_ to _,,_)

\end{code}
}

There are some important notions which are missing but are derivable from the syntax. The groupoid laws on all levels should also be derivable using the J-terms. We will show the construction of some of them in this section.

First of all, one of the important notions is identity context morphism which returns the same value for all substitution. Unfortunately, due to the choice of definition of context morphisms in this model, identity morphism is not primitive. All properties of it have to be proved at the same time because their definitions are dependent on each others.


\begin{code}
IdCm : ∀ Γ → Γ ⇒ Γ

IC-T  : ∀{Γ : Con}(A : Ty Γ)            → A [ IdCm Γ ]T ≡ A
IC-v  : ∀{Γ : Con}{A : Ty Γ}(x : Var A) → x [ IdCm Γ ]V ≅ var x
IC-cm  : ∀{Γ Δ : Con}(δ : Γ ⇒ Δ)        → δ ⊚ IdCm Γ ≡ δ
IC-tm : ∀{Γ : Con}{A : Ty Γ}(a : Tm A) → a [ IdCm Γ ]tm ≅ a
\end{code}

\AgdaHide{
\begin{code}

IdCm ε       = •
IdCm (Γ , A) = (IdCm Γ) +S _ , var v0 ⟦ wk+S+T (IC-T _) ⟫

IC-T {Γ} * = refl
IC-T {Γ} (a =h b) = hom≡ (IC-tm a) (IC-tm b)

IC-v {.(Γ , A)} {.(A +T A)} (v0 {Γ} {A}) = wk-coh ∾ cohOp (wk+S+T (IC-T _))
IC-v {.(Γ , B)} {.(A +T B)} (vS {Γ} {A} {B} x) = wk-coh ∾ wk+S+tm (var x) (IC-v _)

IC-cm • = refl
IC-cm (δ , a) = cm-eq (IC-cm δ) (cohOp [⊚]T ∾ IC-tm a) 

IC-tm (var x) = IC-v x
IC-tm (JJ x δ A) = cohOp (sym [⊚]T) ∾ JJ-eq (IC-cm δ)

\end{code}
}

The projection morphisms follows from the indentity morphism. The first projection is same as weakening.

\begin{code}
pr1 : ∀ {Γ A} → (Γ , A) ⇒ Γ
pr2 : ∀ {Γ A} → Tm {Γ , A} (A [ pr1 ]T)

pr1-wk-T  : ∀{Γ : Con}{A B : Ty Γ} → A [ pr1 ]T ≡ A +T B
pr1-wk-tm : ∀{Γ : Con}{A B : Ty Γ}{a : Tm A} 
          → a [ pr1 ]tm ≅ a +tm B
pr1-wk-cm : ∀{Γ Δ : Con}{A B : Ty Γ}(δ : Γ ⇒ Δ) 
          → δ ⊚ (pr1 {Γ} {B}) ≡ δ +S _

pr2-v0 : ∀ {Γ A} → pr2 {Γ} {A} ≅ var v0

pr-beta : ∀ {Γ A} → (pr1 {Γ} {A} , pr2) ≡ IdCm _
\end{code}

\AgdaHide{
\begin{code}
pr1 {Γ} = IdCm _ +S _

pr1-wk-T = wk+S+T (IC-T _)

pr1-wk-tm {a = a} = wk+S+tm a (IC-tm a)

pr1-wk-cm δ = wk+S+S (IC-cm _)

pr2 = var v0 ⟦ wk+S+T (IC-T _) ⟫

pr2-v0 {A = A} = cohOp (trans [+S]T (wk-T (IC-T A)))

pr-beta = refl


data IsId : {Γ Δ : Con}(γ : Γ ⇒ Δ) → Set where
  isId-bsc : {γ : ε ⇒ ε} → IsId γ
  isId-ind : {Γ Δ : Con}{γ : Γ ⇒ Δ} → IsId γ → 
             {A : Ty Γ}{B : Ty Δ} → 
             (eq : B [ γ ]T ≡ A) 
           → IsId {Γ , A} {Δ , B} (γ +S _ , var v0 ⟦ wk+S+T eq ⟫)


IC-IsId : {Γ : Con} → IsId (IdCm Γ)
IC-IsId {ε} = isId-bsc
IC-IsId {Γ , A} = isId-ind (IC-IsId {Γ}) (IC-T _)


IC-tm'-v0 : {Γ Δ : Con}{A : Ty Γ}{B : Ty Δ}{γ : (Γ , A) ⇒ (Δ , B)} → IsId γ → var v0 [ γ ]tm ≅ var v0
IC-tm'-v0 (isId-ind isd refl) = wk-coh ∾ cohOp (trans [+S]T refl)

\end{code}




\begin{code}


Id-with : {Γ : Con}{A : Ty Γ} →
           (x : Tm A) 
         → Γ ⇒ (Γ , A)
Id-with x = (IdCm _) , (x ⟦ IC-T _ ⟫)


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
apply-x = wk-coh ∾ (cohOp (IC-T _))

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
fun t a = (t [ Id-with a ]tm) ⟦ sym (trans +T[,]T (IC-T _)) ⟫


\end{code}

}