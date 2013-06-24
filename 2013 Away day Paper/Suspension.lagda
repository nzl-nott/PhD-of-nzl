\AgdaHide{

\begin{code}

{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check #-}

module Suspension where

open import AIOOG
open import AIOOGS2
open import Relation.Binary.PropositionalEquality 
open import Data.Product renaming (_,_ to _,,_)

cohOpV :  {Γ : Con}{A B : Ty Γ}{x : Var A}(p : A ≡ B) → var (subst Var p x) ≅ var x
cohOpV {x = x} refl = refl (var x)

\end{code}
}


Even though we didn't choose suspension to generate the reflexivity, it should be still useful in the future work.

Like all the other definitions, we have to define a set of operations together. In addition we could also prove that the suspension of a contractible context is still contractible.

\begin{code}

ΣC : Con → Con
ΣT : {Γ : Con} → Ty Γ → Ty (ΣC Γ)
Σv : {Γ : Con}(A : Ty Γ) → Var A → Var (ΣT A)
Σtm : {Γ : Con}(A : Ty Γ) → Tm A → Tm (ΣT A)
Σs : {Γ Δ : Con} → Γ ⇒ Δ → ΣC Γ ⇒ ΣC Δ
ΣC-Contr : (Δ : Con) → isContr Δ → isContr (ΣC Δ)


\end{code}

The suspension of a context is to substitute the base type with the equality of two variables of base type for all occurences. So the base case for a suspension is a context contains two variables of base type. That means we can declare new variables whose type is the equality of these two variables. 

\begin{code}

ΣC ε = ε , * , *
ΣC (Γ , A) = ΣC Γ , ΣT A

*' : {Γ : Con} → Ty (ΣC Γ)
*' {ε} = var (vS v0) =h var v0
*' {Γ , A} = *' {Γ} +T ΣT A

_=h'_ : {Γ : Con}{A : Ty Γ}(a b : Tm A) → Ty (ΣC Γ)
a =h' b = Σtm _ a =h Σtm _ b

ΣT {Γ} * = *' {Γ}
ΣT (a =h b) = a =h' b

\end{code}

There are some lemmas which are neceesary for the definitions. The suspension of terms and context morphisms are too cumbersome to present here.


\begin{code}

ΣT[+T]   : {Γ : Con}(A : Ty Γ)(B : Ty Γ) 
         → ΣT (A +T B) ≡ ΣT A +T ΣT B
Σtm[+tm] : {Γ : Con}{A : Ty Γ}(a : Tm A)(B : Ty Γ) 
         → Σtm _ (a +tm B) ≅ Σtm _ a +tm ΣT B

\end{code}

\AgdaHide{
\begin{code}

ΣT[+T] * B = refl
ΣT[+T] (_=h_ {A} a b) B = hom≡ (Σtm[+tm] a B) (Σtm[+tm] b B)

ΣT[Σs]T : {Γ Δ : Con}(A : Ty Δ) → (δ : Γ ⇒ Δ) → (ΣT A) [ Σs δ ]T ≡ ΣT (A [ δ ]T)

Σv .(A +T A) (v0 {Γ} {A}) = subst Var (sym (ΣT[+T] A A)) v0
Σv .(A +T B) (vS {Γ} {A} {B} x) = subst Var (sym (ΣT[+T] {_} A B)) (vS (Σv A x))

Σtm A (var x) = var (Σv A x)
Σtm .(A [ δ ]T) (JJ x δ A) = JJ (ΣC-Contr _ x) (Σs δ) (ΣT A) ⟦ sym (ΣT[Σs]T A δ) ⟫



Σs {Γ} {Δ , A} (γ , a) = (Σs γ) , Σtm (A [ γ ]T) a ⟦ ΣT[Σs]T A γ ⟫
Σs {ε} • = IdCm _
Σs {Γ , A} • = Σs {Γ} • +S ΣT A


cohOpΣtm : ∀ {Δ : Con}{A B : Ty Δ}(t : Tm B)(p : A ≡ B) → Σtm A (t ⟦ p ⟫) ≅ Σtm B t
cohOpΣtm t refl = refl _

Σv[Σs]tm : {Γ Δ : Con}(A : Ty Δ)(x : Var A)(δ : Γ ⇒ Δ) → (var (Σv A x)) [ Σs δ ]tm ≅ Σtm (A [ δ ]T) ((var x) [ δ ]tm)
Σv[Σs]tm .(A +T A) (v0 {Γ₁} {A}) (δ , a) = cohOpV (sym (ΣT[+T] A A)) ◃V Σs (δ , a) ∾ wk-coh ∾ cohOp (ΣT[Σs]T A δ) ∾ cohOpΣtm a +T[,]T -¹

Σv[Σs]tm .(A +T B) (vS {Γ₁} {A} {B} x) (δ , b) = cohOpV (sym (ΣT[+T] A B)) ◃V Σs (δ , b) ∾
                                                  wk-coh ∾ Σv[Σs]tm A x δ ∾ cohOpΣtm (x [ δ ]V) +T[,]T -¹


Σs⊚ : ∀ {Δ Δ₁ Γ}(δ : Δ ⇒ Δ₁)(γ : Γ ⇒ Δ) → Σs (δ ⊚ γ) ≡ Σs δ ⊚ Σs γ

Σtm[Σs]tm : ∀ {Γ Δ : Con}{A : Ty Δ}(a : Tm A)(δ : Γ ⇒ Δ) → 
              (Σtm A a) [ Σs δ ]tm ≅ Σtm (A [ δ ]T) (a [ δ ]tm)
Σtm[Σs]tm {Γ} {Δ} {A} (var x) δ = Σv[Σs]tm A x δ
Σtm[Σs]tm {Γ} {Δ} (JJ {Δ = Δ₁} x δ A) δ₁ = cohOp (sym (ΣT[Σs]T A δ)) ◃ Σs δ₁ ∾ cohOp (sym [⊚]T) ∾ JJ-eq (sym (Σs⊚ δ δ₁)) ∾ (cohOpΣtm (JJ x (δ ⊚ δ₁) A) (sym [⊚]T) ∾ cohOp (sym (ΣT[Σs]T A (δ ⊚ δ₁)))) -¹

Σs•-left-id : ∀{Γ Δ : Con}(γ : Γ ⇒ Δ) → Σs {Γ} • ≡ Σs {Δ} • ⊚ Σs γ
Σs•-left-id {ε} {ε} • = refl
Σs•-left-id {ε} {Δ , A} (γ , a) = trans (Σs•-left-id {ε} {Δ} γ) (sym (⊚wk (ΣT A) (Σs {Δ} •) (Σs γ) _))
Σs•-left-id {Γ , A} {ε} • = trans (cong (λ x → x +S ΣT A) (Σs•-left-id {Γ} {ε} •)) (cm-eq (cm-eq refl ([+S]V (vS v0) {Σs {Γ} •} -¹)) ([+S]V v0 {Σs {Γ} •} -¹))
Σs•-left-id {Γ , A} {Δ , A₁} (γ , a) = trans (Σs•-left-id γ) (sym (⊚wk (ΣT A₁) (Σs {Δ} •) (Σs γ) _)) 

Σs⊚ • γ = Σs•-left-id γ
Σs⊚ {Δ} (_,_ δ {A} a) γ = cm-eq (Σs⊚ δ γ) (cohOp (ΣT[Σs]T A (δ ⊚ γ)) ∾ cohOpΣtm (a [ γ ]tm) [⊚]T ∾ (cohOp [⊚]T ∾ cohOp (ΣT[Σs]T A δ) ◃ Σs γ ∾ Σtm[Σs]tm a γ) -¹) 


ΣT[+S]T : ∀{Γ Δ : Con}(A : Ty Δ)(δ : Γ ⇒ Δ)(B : Ty Γ) → ΣT A [ Σs δ +S ΣT B ]T ≡ ΣT (A [ δ ]T) +T ΣT B
ΣT[+S]T A δ B = trans [+S]T (cong (λ x → x +T ΣT B) (ΣT[Σs]T A δ))

ΣsDis : ∀{Γ Δ : Con}{A : Ty Δ}(δ : Γ ⇒ Δ)(a : Tm (A [ δ ]T))(B : Ty Γ) → (Σs {Γ} {Δ , A} (δ , a)) +S ΣT B ≡ Σs δ +S ΣT B , ((Σtm (A [ δ ]T) a) +tm ΣT B) ⟦ ΣT[+S]T A δ B ⟫
ΣsDis {Γ} {Δ} {A} δ a B = cm-eq refl (wk-coh+ ∾ (cohOp (trans [+S]T (cong (λ x → x +T ΣT B) (ΣT[Σs]T A δ))) ∾ cong+tm (ΣT[Σs]T A δ)) -¹)

ΣsΣT : ∀ {Γ Δ : Con}(δ : Γ ⇒ Δ)(B : Ty Γ) → Σs (δ +S B) ≡ Σs δ +S ΣT B
ΣsΣT {ε} • _ = refl
ΣsΣT {Γ , A} • _ = refl
ΣsΣT (_,_ δ {A} a) B = cm-eq (ΣsΣT δ B) (cohOp (ΣT[Σs]T A (δ +S B)) ∾ cohOpΣtm (a +tm B) [+S]T ∾ Σtm[+tm] a B ∾ cong+tm (ΣT[Σs]T A δ) ∾ wk-coh+ -¹) 

*'[Σs]T : {Γ Δ : Con} → (δ : Γ ⇒ Δ) → *' {Δ} [ Σs δ ]T ≡ *' {Γ}
*'[Σs]T {ε} • = refl
*'[Σs]T {Γ , A} • = trans (sym (hom≡ ([+S]V (vS v0) {Σs {Γ} •} -¹) ([+S]V v0 {Σs {Γ} •} -¹))) (cong (λ x → x +T ΣT A) (*'[Σs]T {Γ} •)) 
*'[Σs]T {Γ} {Δ , A} (γ , a) = trans +T[,]T (*'[Σs]T γ)

ΣT[Σs]T * δ = *'[Σs]T δ
ΣT[Σs]T (_=h_ {A} a b) δ = hom≡ (Σtm[Σs]tm a δ) (Σtm[Σs]tm b δ)



Σtm[+tm] {A = A} (var x) B = cohOpV (sym (ΣT[+T] A B))
Σtm[+tm] {Γ} (JJ {Δ = Δ} x δ A) B = cohOpΣtm (JJ x (δ +S B) A) (sym [+S]T) ∾ cohOp (sym (ΣT[Σs]T A (δ +S B))) ∾ JJ-eq (ΣsΣT δ B) ∾ cohOp (sym [+S]T) -¹ ∾ cong+tm (sym (ΣT[Σs]T A δ))

ΣC-Contr .(ε , *) c* = ext c* v0
ΣC-Contr .(Γ , A , (var (vS x) =h var v0)) (ext {Γ} r {A} x) = subst (λ y → isContr (ΣC Γ , ΣT A , y)) (hom≡ (cohOpV (sym (ΣT[+T] A A)) -¹) (cohOpV (sym (ΣT[+T] A A)) -¹))
                                                                (ext (ΣC-Contr Γ r) {ΣT A} (Σv A x))


\end{code}
}