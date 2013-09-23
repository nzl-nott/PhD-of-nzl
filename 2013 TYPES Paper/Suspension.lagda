\AgdaHide{

\begin{code}

{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check #-}

module Suspension where

open import AIOOG
open import AIOOGS2
open import Relation.Binary.PropositionalEquality 
open import Data.Product renaming (_,_ to _,,_)
open import Data.Empty
open import Data.Nat


1-1cm-same : {Γ : Con}{A B : Ty Γ} → 
            B ≡ A → (Γ , A) ⇒ (Γ , B)
1-1cm-same eq = pr1 , pr2 ⟦ congT eq ⟫ 


1-1cm-same-T : {Γ : Con}{A B : Ty Γ} → 
               (eq : B ≡ A) → (A +T B) [ 1-1cm-same eq ]T ≡ A +T A
1-1cm-same-T eq = trans +T[,]T (trans [+S]T (wk-T (IC-T _)))


1-1cm-same-tm : ∀ {Γ : Con}{A : Ty Γ}{B : Ty Γ} → 
               (eq : B ≡ A)(a : Tm A) → (a +tm B) [ 1-1cm-same eq ]tm ≅ (a +tm A)
1-1cm-same-tm eq a = +tm[,]tm a ∾ [+S]tm a ∾ cong+tm (IC-tm a)

1-1cm-same-v0 : ∀ {Γ : Con}{A B : Ty Γ} → 
               (eq : B ≡ A) → var v0 [ 1-1cm-same eq ]tm ≅ var v0
1-1cm-same-v0 eq = wk-coh ∾ cohOp (congT eq) ∾ pr2-v0


_++_ : Con → Con → Con

cor : {Γ : Con}(Δ : Con) → (Γ ++ Δ) ⇒ Δ

repeat-p1 : {Γ : Con}(Δ : Con) → (Γ ++ Δ) ⇒ Γ

Γ ++ ε = Γ
Γ ++ (Δ , A) = Γ ++ Δ , A [ cor Δ ]T


repeat-p1 ε = IdCm _
repeat-p1 (Δ , A) = repeat-p1 Δ ⊚ pr1


cor ε = •
cor (Δ , A) = (cor Δ +S _) , var v0 ⟦ [+S]T ⟫



_++cm_ : ∀ {Γ Δ Θ} → Γ ⇒ Δ → Γ ⇒ Θ → Γ ⇒ (Δ ++ Θ)
cor-inv : ∀ {Γ Δ Θ} → {γ : Γ ⇒ Δ}(δ : Γ ⇒ Θ) → cor Θ ⊚ (γ ++cm δ) ≡ δ

γ ++cm • = γ
γ ++cm (δ , a) = γ ++cm δ , a ⟦ trans (sym [⊚]T) (congT2 (cor-inv _)) ⟫ 

cor-inv • = refl
cor-inv (δ , a) = cm-eq (trans (⊚wk _) (cor-inv δ)) 
        (cohOp [⊚]T ∾ congtm (cohOp [+S]T) 
        ∾ cohOp +T[,]T 
        ∾ cohOp (trans (sym [⊚]T) (congT2 (cor-inv _))))


id-cm++ : {Γ : Con}(Δ Θ : Con) → (Δ ⇒ Θ) → (Γ ++ Δ) ⇒ (Γ ++ Θ)
id-cm++ Δ Θ γ = repeat-p1 Δ ++cm (γ ⊚ cor _)

\end{code}
}


\subsection{Lifting and replacing functions}

For arbitrary type $A$ in context $\Gamma$, there should be a context which only contains the minimum required variables for it.
We design an approach to filter these variables out. Briefly speaking, we construct 

The minimum context could be a basis for a contractible context. We find that if we have a contractible context $\Delta$ and we replace the $*$ in $\Delta$ with $A$, technically we reconstruct a similar context to $\Delta$ to the right of the minimum context for $A$, then the resulting context is also contractible. Then there should be a set of lifting functions for types, terms and morphisms. In fact we could relax the coverage of the lifting functions to any context. It provides us a general method to establish terms. Later we will use them to prove the groupoid laws.


\paragraph{Suspension functions}

First we need to construct the minimum context. We define the suspension functions which lift everything one level higher by replacing the base type $*$ with the morphism between two variables of type $*$ for all occurences.  That means we can declare new variables whose type is the morphism between these two variables just as we can declare new variables of base type $*$ in empty context.


\begin{code}

ΣC : Con → Con
ΣT : {Γ : Con} → Ty Γ → Ty (ΣC Γ)
Σv : {Γ : Con}{A : Ty Γ} → Var A → Var (ΣT A)
Σtm : {Γ : Con}{A : Ty Γ} → Tm A → Tm (ΣT A)
Σs : {Γ Δ : Con} → Γ ⇒ Δ → ΣC Γ ⇒ ΣC Δ
ΣC-Contr : (Δ : Con) → isContr Δ → isContr (ΣC Δ)

\end{code}

For the definition and other lemmas for these functions, they are too cumbersome to present here but are available online.
\AgdaHide{
\begin{code}

ΣC ε = ε , * , *
ΣC (Γ , A) = ΣC Γ , ΣT A


*' : {Γ : Con} → Ty (ΣC Γ)
*' {ε} = var (vS v0) =h var v0
*' {Γ , A} = *' {Γ} +T _

ΣT {Γ} * = *' {Γ}
ΣT (a =h b) = Σtm a =h Σtm b


Σs• : (Γ : Con) → ΣC Γ ⇒ ΣC ε
Σs• ε = IdCm _
Σs• (Γ , A) = Σs• Γ +S _

\end{code}
}

\begin{code}

ΣT[+T]   : {Γ : Con}(A : Ty Γ)(B : Ty Γ) 
         → ΣT (A +T B) ≡ ΣT A +T ΣT B
Σtm[+tm] : {Γ : Con}{A : Ty Γ}(a : Tm A)(B : Ty Γ) 
         → Σtm (a +tm B) ≅ Σtm a +tm ΣT B

ΣT[Σs]T : {Γ Δ : Con}(A : Ty Δ)(δ : Γ ⇒ Δ) 
        → (ΣT A) [ Σs δ ]T ≡ ΣT (A [ δ ]T)

\end{code}

\AgdaHide{
\begin{code}

ΣT[+T] * B = refl
ΣT[+T] (_=h_ {A} a b) B = hom≡ (Σtm[+tm] a B) (Σtm[+tm] b B)

Σv {.(Γ , A)} {.(A +T A)} (v0 {Γ} {A}) = subst Var (sym (ΣT[+T] A A)) v0
Σv {.(Γ , B)} {.(A +T B)} (vS {Γ} {A} {B} x) = subst Var (sym (ΣT[+T] {_} A B)) (vS (Σv x))


Σtm (var x) = var (Σv x)
Σtm (JJ x δ A) = JJ (ΣC-Contr _ x) (Σs δ) (ΣT A) ⟦ sym (ΣT[Σs]T A δ) ⟫


Σtm-p1 : {Γ : Con}(A : Ty Γ) → Σtm {Γ , A} (var v0) ≅ var v0 
Σtm-p1 A = cohOpV (sym (ΣT[+T] A A))

Σtm-p2 : {Γ : Con}(A B : Ty Γ)(x : Var A) → var (Σv (vS {B = B} x)) ≅ var (vS (Σv x))
Σtm-p2 {Γ} A B x = cohOpV (sym (ΣT[+T] A B))

Σtm-p2-sp : {Γ : Con}(A : Ty Γ)(B : Ty (Γ , A)) → Σtm {Γ , A , B} (var (vS v0)) ≅ (var v0) +tm _
Σtm-p2-sp A B = Σtm-p2 (A +T A) B v0 ∾  cong+tm (Σtm-p1 A)

Σs {Γ} {Δ , A} (γ , a) = (Σs γ) , Σtm a ⟦ ΣT[Σs]T A γ ⟫ 
Σs {Γ} • = Σs• Γ


cohOpΣtm : ∀ {Δ : Con}{A B : Ty Δ}(t : Tm B)(p : A ≡ B) → Σtm (t ⟦ p ⟫) ≅ Σtm t
cohOpΣtm t refl = refl _

Σs⊚ : ∀ {Δ Δ₁ Γ}(δ : Δ ⇒ Δ₁)(γ : Γ ⇒ Δ) → Σs (δ ⊚ γ) ≡ Σs δ ⊚ Σs γ

Σv[Σs]v :  ∀ {Γ Δ : Con}{A : Ty Δ}(x : Var A)(δ : Γ ⇒ Δ) → Σv x [ Σs δ ]V ≅ Σtm (x [ δ ]V)
Σv[Σs]v (v0 {Γ} {A}) (δ , a) = congtm (Σtm-p1 A) ∾ wk-coh ∾ cohOp (ΣT[Σs]T A δ) ∾ cohOpΣtm a +T[,]T -¹
Σv[Σs]v (vS {Γ} {A} {B} x) (δ , a) = congtm (Σtm-p2 A B x) ∾
                                       +tm[,]tm (Σtm (var x)) ∾
                                       Σv[Σs]v x δ ∾ cohOpΣtm (x [ δ ]V) +T[,]T -¹

Σtm[Σs]tm : ∀ {Γ Δ : Con}{A : Ty Δ}(a : Tm A)(δ : Γ ⇒ Δ) → 
              (Σtm a) [ Σs δ ]tm ≅ Σtm (a [ δ ]tm)
Σtm[Σs]tm (var x) δ = Σv[Σs]v x δ
Σtm[Σs]tm {Γ} {Δ} (JJ {Δ = Δ₁} x δ A) δ₁ = congtm (cohOp (sym (ΣT[Σs]T A δ))) 
                      ∾ cohOp (sym [⊚]T) 
                      ∾ JJ-eq (sym (Σs⊚ δ δ₁)) 
                      ∾ (cohOpΣtm (JJ x (δ ⊚ δ₁) A) (sym [⊚]T) 
                      ∾ cohOp (sym (ΣT[Σs]T A (δ ⊚ δ₁)))) -¹

Σs•-left-id : ∀{Γ Δ : Con}(γ : Γ ⇒ Δ) → Σs {Γ} • ≡ Σs {Δ} • ⊚ Σs γ
Σs•-left-id {ε} {ε} • = refl
Σs•-left-id {ε} {Δ , A} (γ , a) = trans (Σs•-left-id γ) (sym (⊚wk (Σs• Δ)))
Σs•-left-id {Γ , A} {ε} • = trans (cong (λ x → x +S ΣT A) (Σs•-left-id {Γ} {ε} •)) (cm-eq (cm-eq refl ([+S]V (vS v0) {Σs• Γ} -¹)) ([+S]V v0 {Σs• Γ} -¹))
Σs•-left-id {Γ , A} {Δ , A₁} (γ , a) = trans (Σs•-left-id γ) (sym (⊚wk (Σs• Δ))) 

Σs⊚ • γ = Σs•-left-id γ
Σs⊚ {Δ} (_,_ δ {A} a) γ = cm-eq (Σs⊚ δ γ) (cohOp (ΣT[Σs]T A (δ ⊚ γ)) ∾ cohOpΣtm (a [ γ ]tm) [⊚]T ∾ (cohOp [⊚]T ∾ congtm (cohOp (ΣT[Σs]T A δ)) ∾ Σtm[Σs]tm a γ) -¹) 


ΣT[+S]T : ∀{Γ Δ : Con}(A : Ty Δ)(δ : Γ ⇒ Δ)(B : Ty Γ) → ΣT A [ Σs δ +S ΣT B ]T ≡ ΣT (A [ δ ]T) +T ΣT B
ΣT[+S]T A δ B = trans [+S]T (wk-T (ΣT[Σs]T A δ))

ΣsDis : ∀{Γ Δ : Con}{A : Ty Δ}(δ : Γ ⇒ Δ)(a : Tm (A [ δ ]T))(B : Ty Γ) → (Σs {Γ} {Δ , A} (δ , a)) +S ΣT B ≡ Σs δ +S ΣT B , ((Σtm a) +tm ΣT B) ⟦ ΣT[+S]T A δ B ⟫
ΣsDis {Γ} {Δ} {A} δ a B = cm-eq refl (wk-coh+ ∾ (cohOp (trans [+S]T (wk-T (ΣT[Σs]T A δ))) ∾ cong+tm2 (ΣT[Σs]T A δ)) -¹)

ΣsΣT : ∀ {Γ Δ : Con}(δ : Γ ⇒ Δ)(B : Ty Γ) → Σs (δ +S B) ≡ Σs δ +S ΣT B
ΣsΣT • _ = refl
ΣsΣT (_,_ δ {A} a) B = cm-eq (ΣsΣT δ B) (cohOp (ΣT[Σs]T A (δ +S B)) ∾ cohOpΣtm (a +tm B) [+S]T ∾ Σtm[+tm] a B ∾ cong+tm2 (ΣT[Σs]T A δ) ∾ wk-coh+ -¹) 

*'[Σs]T : {Γ Δ : Con} → (δ : Γ ⇒ Δ) → *' {Δ} [ Σs δ ]T ≡ *' {Γ}
*'[Σs]T {ε} • = refl
*'[Σs]T {Γ , A} • = trans ([+S]T {A = *' {ε}} {δ = Σs {Γ} •}) (wk-T (*'[Σs]T {Γ} •))
*'[Σs]T {Γ} {Δ , A} (γ , a) = trans +T[,]T (*'[Σs]T γ)

ΣT[Σs]T * δ = *'[Σs]T δ
ΣT[Σs]T (_=h_ {A} a b) δ = hom≡ (Σtm[Σs]tm a δ) (Σtm[Σs]tm b δ)

Σtm[+tm] {A = A} (var x) B = cohOpV (sym (ΣT[+T] A B))
Σtm[+tm] {Γ} (JJ {Δ = Δ} x δ A) B = cohOpΣtm (JJ x (δ +S B) A) (sym [+S]T) ∾ cohOp (sym (ΣT[Σs]T A (δ +S B))) ∾ JJ-eq (ΣsΣT δ B) ∾ cohOp (sym [+S]T) -¹ ∾ cong+tm2 (sym (ΣT[Σs]T A δ))


ΣC-Contr .(ε , *) c* = ext c* v0
ΣC-Contr .(Γ , A , (var (vS x) =h var v0)) (ext {Γ} r {A} x) = subst (λ y → isContr (ΣC Γ , ΣT A , y))
                                                                 (hom≡ (cohOpV (sym (ΣT[+T] A A)) -¹)
                                                                  (cohOpV (sym (ΣT[+T] A A)) -¹))
                                                                 (ext (ΣC-Contr Γ r) {ΣT A} (Σv x))


congΣtm : {Γ : Con}{A B : Ty Γ}{a : Tm A}{b : Tm B} → a ≅ b → Σtm a ≅ Σtm b
congΣtm {Γ} {.B} {B} {.b} {b} (refl .b) = refl _
\end{code}
}


\paragraph{Lifting functions}

To define lifting function, we only need to recursively call suspension functions with respect to the level of type $A$. To make the opeartion more clearly, for instance a context $x : * , y : * , p : x = y$ will be lifted to $..., x : A, y : A, p : x = y$ while the first part is the minimum context for $A$.

\begin{code}
lift-C : {Γ : Con}(A : Ty Γ) → Con → Con

lift-T : {Γ Δ : Con}(A : Ty Γ) → Ty Δ → Ty (lift-C A Δ)

lift-tm : {Γ Δ : Con}(A : Ty Γ){B : Ty Δ} → Tm B → Tm (lift-T A B)

\end{code}

\AgdaHide{
\begin{code}

lift-cm : {Γ Δ Θ : Con}(A : Ty Γ) → Θ ⇒ Δ → (lift-C A Θ) ⇒ (lift-C A Δ)

lift-C * Δ = Δ
lift-C (_=h_ {A} a b) Δ = ΣC (lift-C A Δ)

lift-T * B = B
lift-T (_=h_ {A} a b) B = ΣT (lift-T A B)
  
lift-tm * t = t
lift-tm (_=h_ {A} a b) t = Σtm (lift-tm A t)

lift-cm * γ = γ
lift-cm (_=h_ {A} a b) γ = Σs (lift-cm A γ)

\end{code}
}

We observe that while the context to be lifted is empty, it is just the minimum context for type $A$. A context morphism which filters out the minimum context would be very useful later since we can turn lifted types and terms back to the ones for the orignal context. We name it as \emph{minimum morphism}.

\begin{code}

minimum-cm : ∀ {Γ : Con}(A : Ty Γ) → Γ ⇒ lift-C A ε

\end{code}


\AgdaHide{
\begin{code}

ΣC-p1 :{Γ : Con}(A : Ty Γ) → ΣC (Γ , A) ≡ ΣC Γ , ΣT A
ΣC-p1 * = refl
ΣC-p1 (a =h b) = refl


lift-C-p1 : {Γ Δ : Con}(A : Ty Γ)(B : Ty Δ) → lift-C A (Δ , B) ≡ (lift-C A Δ , lift-T A B)
lift-C-p1 * B = refl
lift-C-p1 (_=h_ {A} a b) B = cong ΣC (lift-C-p1 A B)

-- to split lift-C

lift-C-cm-spl' : {Γ Δ : Con}(A : Ty Γ)(B : Ty Δ) → 
               (lift-C A Δ , lift-T A B) ≡ lift-C A (Δ , B)
lift-C-cm-spl' * B = refl
lift-C-cm-spl' (_=h_ {A} a b) B = cong ΣC (lift-C-cm-spl' A B)

lift-C-cm-spl : {Γ Δ : Con}(A : Ty Γ)(B : Ty Δ) → 
               (lift-C A Δ , lift-T A B) ⇒ lift-C A (Δ , B)
lift-C-cm-spl * B = IdCm _
lift-C-cm-spl (_=h_ {A} a b) B = Σs (lift-C-cm-spl A B)


lift-C-cm-spl-¹ : {Γ Δ : Con}(A : Ty Γ)(B : Ty Δ) → 
                lift-C A (Δ , B) ⇒ (lift-C A Δ , lift-T A B)
lift-C-cm-spl-¹ * B = IdCm _
lift-C-cm-spl-¹ (_=h_ {A} a b) B = Σs (lift-C-cm-spl-¹ A B)


lift-C-cm-spl2 : {Γ : Con}(A : Ty Γ)
              → (lift-C A ε , lift-T A * ,  lift-T A * +T _) ⇒ ΣC (lift-C A ε)
lift-C-cm-spl2 * = IdCm _
lift-C-cm-spl2 (_=h_ {A} a b) = Σs (lift-C-cm-spl2 A) ⊚ 1-1cm-same (ΣT[+T] (lift-T A *) (lift-T A *))


lift-T-wk : {Γ Δ : Con}(A : Ty Γ)(B : Ty Δ) → (lift-T A *) [ lift-C-cm-spl A B ]T ≡ lift-T A * +T _
lift-T-wk * B = refl
lift-T-wk (_=h_ {A} a b) B = trans (ΣT[Σs]T (lift-T A *) (lift-C-cm-spl A B)) (trans (cong ΣT (lift-T-wk A B)) (ΣT[+T] (lift-T A *) (lift-T A B)))

lift-T-p1 : ∀ {Γ : Con}(A : Ty Γ) → lift-T A * [ minimum-cm A ]T ≡ A

lift-T-p2 : {Γ Δ : Con}(A : Ty Γ){B : Ty Δ}{a b : Tm B} → lift-T A (a =h b) ≡ (lift-tm A a =h lift-tm A b)
lift-T-p2 * = refl
lift-T-p2 (_=h_ {A} _ _) = cong ΣT (lift-T-p2 A)


lift-T-p3 : {Γ Δ : Con}(A : Ty Γ){B C : Ty Δ} → lift-T A (C +T B) [ lift-C-cm-spl A B ]T ≡ lift-T A C +T _ 
lift-T-p3 * = trans +T[,]T (wk+S+T (IC-T _))
lift-T-p3 (_=h_ {A} a b) {B} {C} = trans (ΣT[Σs]T (lift-T A (C +T B)) (lift-C-cm-spl A B)) (trans (cong ΣT (lift-T-p3 A)) (ΣT[+T] (lift-T A C) (lift-T A B)))


minimum-cm * = •
minimum-cm {Γ} (_=h_ {A} a b) = lift-C-cm-spl2 A ⊚ ((minimum-cm A , (a ⟦ lift-T-p1 A ⟫)) , (wk-tm (b ⟦ lift-T-p1 A ⟫)))


lift-C-ε-Contr :  ∀ {Γ Δ : Con}(A : Ty Γ) → isContr Δ → isContr (lift-C A Δ)
lift-C-ε-Contr * isC = isC
lift-C-ε-Contr (_=h_ {A} a b) isC = ΣC-Contr _ (lift-C-ε-Contr A isC)


wk-lift : ∀ {Γ : Con}(A : Ty Γ)(a : Tm A) → a ⟦ lift-T-p1 A ⟫ ≅ a
wk-lift A a = cohOp (lift-T-p1 A)

fci-l1 : ∀ {Γ : Con}(A : Ty Γ) → ΣT (lift-T A *) [ lift-C-cm-spl2 A ]T ≡ (var (vS v0) =h var v0)

fci-l1 * = refl
fci-l1 {Γ} (_=h_ {A} a b) = trans [⊚]T (trans
                                      (congT
                                       (trans (ΣT[Σs]T (ΣT (lift-T A *)) (lift-C-cm-spl2 A))
                                        (cong ΣT (fci-l1 A))))
                                      (hom≡
                                         (congtm (Σtm-p2-sp (lift-T A *) (lift-T A * +T lift-T A *)) ∾
                                          1-1cm-same-tm (ΣT[+T] (lift-T A *) (lift-T A *)) (var v0))
                                         (congtm (Σtm-p1 (lift-T A * +T lift-T A *)) ∾
                                            1-1cm-same-v0 (ΣT[+T] (lift-T A *) (lift-T A *)))) )

lift-T-p1  * = refl
lift-T-p1 (_=h_ {A} a b) = trans [⊚]T (trans (congT (fci-l1 A)) (hom≡ (prf a) (prf b)))
  where
    prf : (a : Tm A) → ((a ⟦ lift-T-p1 A ⟫) ⟦ +T[,]T ⟫) ⟦ +T[,]T ⟫ ≅ a
    prf a = wk-coh ∾ wk-coh ∾ wk-lift A a
 


lift-tm-p1 : {Γ Δ : Con}(A : Ty Γ){B : Ty Δ} → lift-tm A (var v0) [ lift-C-cm-spl A B ]tm ≅ var v0
lift-tm-p1 * {B} = wk-coh ∾ cohOp (wk+S+T (IC-T _))
lift-tm-p1 (_=h_ {A} a b) {B} = Σtm[Σs]tm (lift-tm A (var v0)) (lift-C-cm-spl A B) ∾ congΣtm (lift-tm-p1 A) ∾ cohOpV (sym (ΣT[+T] (lift-T A B) (lift-T A B)))



lift-tm-p2 : {Γ Δ : Con}(A : Ty Γ){B C : Ty Δ}(x : Var B) → (lift-tm A (var (vS x))) [ lift-C-cm-spl A C ]tm ≅ lift-tm A (var x) +tm _
lift-tm-p2 * x = wk-coh ∾ [+S]V x ∾ cong+tm (IC-v x)
lift-tm-p2 {Γ} {Δ} (_=h_ {A} a b) {B} {C} x = Σtm[Σs]tm (lift-tm A (var (vS x))) (lift-C-cm-spl A C) ∾
                                               congΣtm (lift-tm-p2 {Γ} {Δ} A {B} x) ∾
                                               Σtm[+tm] (lift-tm A (var x)) (lift-T A C)


\end{code}
}

These lifting functions are not ideal for practical use since the minimum context is too special. A better operation is to just append the lifted part with the original context $\Gamma$ for type $A$.

\paragraph{Replacing functions}

The "true" lift operations which we call replacing functions will do the work. Given a type $A$ in a context $\Gamma$, it will return $\Gamma , A$ if we replace the base type in context $\epsilon , *$ with $A$.

The new context actually contains two parts, the first is the same as $\Gamma$, and the second is the lifted $\Delta$. It is not as simple as the combination of the orignal context and the whole lifted context. What we need to do is to utilise the minimum morphism to substitute the lifted context without the minimum context part which already exists in $\Gamma$.

Therefore we have two substitutions and the second one is essential in the definition of lifting operator for types and terms.
Intuitively speaking, it maps the original basis for type $A$ in $\Gamma$ to the newly created basis for the lifted base type in lifted context. All the other higher structures are just the tail of the lifted context (except the first part).

\begin{code}

rpl-C : {Γ : Con}(A : Ty Γ) → Con → Con


rpl-T : {Γ Δ : Con}(A : Ty Γ) → Ty Δ → Ty (rpl-C A Δ)


rpl-tm : {Γ Δ : Con}(A : Ty Γ){B : Ty Δ} → 
         Tm B
      → Tm (rpl-T A B)

\end{code}


\begin{code}
filter-cm : {Γ : Con}(Δ : Con)(A : Ty Γ) → rpl-C A Δ ⇒ lift-C A Δ

rpl-pr1  : {Γ : Con}(Δ : Con)(A : Ty Γ) → rpl-C A Δ ⇒ Γ
\end{code}

\AgdaHide{
\begin{code}

{-
rpl-cm : {Γ Δ Θ : Con}(A : Ty Γ) → Θ ⇒ Δ → (rpl-C A Θ) ⇒ (rpl-C A Δ)
-}

rpl-C {Γ} A ε = Γ
rpl-C A (Δ , B) = rpl-C A Δ , rpl-T A B

rpl-pr1 ε A = IdCm _
rpl-pr1 (Δ , A) A₁ = rpl-pr1 Δ A₁ +S _

rpl-T A B = lift-T A B [ filter-cm _ A ]T

filter-cm ε A = minimum-cm A
filter-cm (Δ , A) A₁ =  lift-C-cm-spl A₁ A ⊚ ((filter-cm Δ A₁ +S _) , var v0 ⟦ [+S]T ⟫)


rpl-T-p1 : {Γ : Con}(Δ : Con)(A : Ty Γ) → rpl-T A * ≡ A [ rpl-pr1 Δ A ]T
rpl-T-p1 ε A = trans (lift-T-p1 A) (sym (IC-T _))
rpl-T-p1 (Δ , A) A₁ = trans [⊚]T (trans (congT (lift-T-wk A₁ A)) (trans +T[,]T (trans [+S]T (trans (wk-T (rpl-T-p1 Δ A₁)) (sym [+S]T)))))

rpl-tm A a = lift-tm A a [ filter-cm _ A ]tm


rpl-tm-id : {Γ : Con}{A : Ty Γ} → Tm A → Tm (rpl-T {Δ = ε} A *)
rpl-tm-id x =  x ⟦ lift-T-p1 _ ⟫


rpl-T-p2 : {Γ : Con}(Δ : Con)(A : Ty Γ){B : Ty Δ}{a b : Tm B}  → rpl-T A (a =h b) ≡ (rpl-tm A a =h rpl-tm A b)
rpl-T-p2 Δ A = congT (lift-T-p2 A)


rpl-T-p3 : {Γ : Con}(Δ : Con)(A : Ty Γ){B : Ty Δ}{C : Ty Δ}
          → rpl-T A (C +T B) ≡ rpl-T A C +T _
rpl-T-p3 _ A = trans [⊚]T (trans (congT (lift-T-p3 A)) (trans +T[,]T [+S]T))

rpl-T-p3-wk : {Γ : Con}(Δ : Con)(A : Ty Γ){B : Ty Δ}{C : Ty Δ}{γ : Γ ⇒ rpl-C A Δ}{b : Tm ((lift-T A B [ filter-cm Δ A ]T) [ γ ]T)}
          → rpl-T A (C +T B) [ γ , b ]T ≡ rpl-T A C [ γ ]T
rpl-T-p3-wk Δ A = trans (congT (rpl-T-p3 Δ A)) +T[,]T

rpl-tm-v0' : {Γ : Con}(Δ : Con)(A : Ty Γ){B : Ty Δ}
           → rpl-tm {Δ = Δ , B} A (var v0) ≅ var v0
rpl-tm-v0' Δ A = [⊚]tm (lift-tm A (var v0)) ∾ congtm (lift-tm-p1 A) ∾ wk-coh ∾ wk-coh+

rpl-tm-v0 : {Γ : Con}(Δ : Con)(A : Ty Γ){B : Ty Δ}{γ : Γ ⇒ rpl-C A Δ}{b : Tm A}{b' : Tm ((lift-T A B [ filter-cm Δ A ]T) [ γ ]T)}
          → (prf : b' ≅ b)
          → rpl-tm {Δ = Δ , B} A (var v0) [ γ , b' ]tm ≅ b
rpl-tm-v0 Δ A prf = congtm (rpl-tm-v0' Δ A) ∾ wk-coh ∾ prf


rpl-tm-vS : {Γ : Con}(Δ : Con)(A : Ty Γ){B C : Ty Δ}{γ : Γ ⇒ rpl-C A Δ}
             {b : Tm (rpl-T A B [ γ ]T)}{x : Var C} → rpl-tm {Δ = Δ , B} A (var (vS x)) [ γ , b ]tm ≅ rpl-tm A (var x) [ γ ]tm
rpl-tm-vS Δ A {x = x} = congtm ([⊚]tm (lift-tm A (var (vS x))) ∾ (congtm (lift-tm-p2 A x))  ∾ +tm[,]tm (lift-tm A (var x))  ∾ ([+S]tm (lift-tm A (var x)))) ∾ +tm[,]tm (lift-tm A (var x) [ filter-cm _ A ]tm)

{-
rpl-cm-p1 : {Γ Δ Θ : Con}{A : Ty Γ}{B : Ty Δ}(γ : Θ ⇒ Δ) → rpl-T A B [ rpl-cm A γ ]T ≡ rpl-T A (B [ γ ]T)

rpl-cm {Θ = Θ} A • = rpl-pr1 Θ A
rpl-cm B (γ , a) = rpl-cm B γ , (rpl-tm B a) ⟦ rpl-cm-p1 γ ⟫


rpl-cm-p1 {Γ} {Θ = Θ} • = {!!}
rpl-cm-p1 (γ , a) = {!!}
-}
-- basic example

base-1 : {Γ : Con}{A : Ty Γ} → rpl-C A (ε , *) ≡ (Γ , A)
base-1 = cong (λ x → _ , x) (lift-T-p1 _)

{-
base-2 : {Γ : Con}{A : Ty Γ} → rpl (ε , * , *) A ≡ (Γ , A , A +T A)
base-2 = Con-eq base-1 {!!}
-}


map-1 : {Γ : Con}{A : Ty Γ} → (Γ , A) ⇒ rpl-C A (ε , *)
map-1 = 1-1cm-same (lift-T-p1 _)

{-
T-1 : {Γ : Con}{A : Ty Γ} → rpl-T (ε , *) A * [ map-1 ]T ≡ A +T A
T-1 {Γ} {A} = trans (congT (rpl-T-p1 (ε , *) A)) (trans {!!} (p1-wk-T {Γ} {A} {A})) -- trans (congT (rpl-T-p2 (ε , *) A)) {!!}

map-2 : {Γ : Con}{A : Ty Γ} → (Γ , A , A +T A) ⇒ rpl (ε , * , *) A
map-2 = (map-1 +S _) , (var v0) ⟦ wk+S+T T-1 ⟫
-}
-- some useful lemmas

rpl*-A : {Γ : Con}{A : Ty Γ} → rpl-T {Δ = ε} A * [ IdCm Γ ]T ≡ A
rpl*-A = trans (IC-T _) (lift-T-p1 _)

rpl*-a : {Γ : Con}(A : Ty Γ){a : Tm A} → rpl-tm {Δ = ε , *} A (var v0) [ IdCm _ , a ⟦ rpl*-A ⟫ ]tm ≅ a
rpl*-a A = rpl-tm-v0 ε A  (cohOp (rpl*-A {A = A}))

rpl*-A2 : {Γ : Con}(A : Ty Γ){a : Tm (rpl-T A (* {ε}) [ IdCm Γ ]T)} 
        → rpl-T A (* {ε , *}) [ IdCm Γ , a ]T ≡ A
rpl*-A2 A = trans (rpl-T-p3-wk ε A) rpl*-A

{-
rpl*-An : {Γ Δ : Con}(A : Ty Γ)(γ : Γ ⇒ lift-C A Δ) -- ( ≡ Γ ++ lift-C A Δ != rpl Δ A)
        → rpl-T Δ A * [ {!!} ]T ≡ A
rpl*-An = {!!}
-}
rpl-xy :  {Γ : Con}(A : Ty Γ)(a b : Tm A)
       → rpl-T {Δ = ε , * , *} A (var (vS v0) =h var v0) [ IdCm Γ , a ⟦ rpl*-A ⟫ , b ⟦ rpl*-A2 A ⟫ ]T
              ≡ (a =h b)
rpl-xy A a b =  trans (congT (rpl-T-p2 (ε , * , *) A)) 
             (hom≡ ((rpl-tm-vS (ε , *) A)  ∾ rpl*-a A) 
                   (rpl-tm-v0 (ε , *) A (cohOp (rpl*-A2 A))))



rpl-sub : (Γ : Con)(A : Ty Γ)(a b : Tm A) →
          Tm (a =h b)
        → Γ ⇒ rpl-C A (ε , * , * , (var (vS v0) =h var v0))
rpl-sub Γ A a b t = IdCm _ , a ⟦ rpl*-A ⟫ , b ⟦ rpl*-A2 A ⟫ , t ⟦ rpl-xy A a b ⟫
  

{-

loop-C : {Γ : Con}(A : Ty Γ) → Con
loop-T : {Γ : Con}(A : Ty Γ) → Ty (loop-C A)
loop-cm : {Γ : Con}(A : Ty Γ) → Γ ⇒ loop-C A
loop-p1 : {Γ : Con}(A : Ty Γ) → loop-T A [ loop-cm A ]T ≡ A

loop-C * = ε
loop-C (_=h_ {A} a b) = loop-C A , loop-T A , loop-T A +T _


loop-T * = *
loop-T (_=h_ {A} a b) = var (vS v0) =h var v0

loop-cm * = •
loop-cm (_=h_ {A} a b) = loop-cm A , a ⟦ loop-p1 A ⟫ , wk-tm (b ⟦ loop-p1 A ⟫)

loop-p1 * = refl
loop-p1 (_=h_ {A} a b) = trans wk-hom (trans wk-hom (cohOp-hom (loop-p1 A)))

loop-Contr : {Γ : Con}(A : Ty Γ) → isContr (loop-C A , loop-T A)
loop-Contr * = c*
loop-Contr (_=h_ {A} _ _) = ext (loop-Contr A) v0



lift' : {Γ : Con}(A : Ty Γ) → Con → Con

lift-T' : {Γ Δ : Con}(A : Ty Γ) → Ty Δ → Ty (lift' A Δ)

lift-tm' : {Γ Δ : Con}(A : Ty Γ){B : Ty Δ} → Tm B → Tm (lift-T' A B)

lift-cm' : {Γ Δ Θ : Con}(A : Ty Γ) → Θ ⇒ Δ → (lift' A Θ) ⇒ (lift' A Δ)


lift'-pr1 : ∀ {Γ : Con}(A : Ty Γ)(Δ : Con) → (lift' A Δ) ⇒ loop-C A

lift' A ε = loop-C A
lift' A (Δ , B) = lift' A Δ , lift-T' A B

lift-T' {Γ} {ε} A * = loop-T A
lift-T' {Γ} {Δ , _} A * = lift-T' {Γ} {Δ} A * +T _ --  loop-T A [ lift'-pr1 A Δ ]T
lift-T' A (a =h b) = lift-tm' A a =h lift-tm' A b
 
lift-tm' A t = {!t!}

lift-cm' A cm = {!!}

lift'-pr1 A ε = IdCm _
lift'-pr1 A (Δ , A₁) = lift'-pr1 A Δ +S _


minimum-cm-p : ∀ {Γ : Con}(A : Ty Γ) → ΣC (lift-C A ε) ⇒ lift-C A ε
minimum-cm-p * = •
minimum-cm-p (_=h_ {A} a b) = Σs (minimum-cm-p A)
-}



\end{code}
}