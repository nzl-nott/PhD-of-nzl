
\AgdaHide{
\begin{code}
module AIOOGS2 where


open import AIOOG
open import Relation.Binary.PropositionalEquality 
open import Data.Product renaming (_,_ to _,,_)

\end{code}
}

There are some important notions which are missing but are derivable from the syntax. The groupoid laws on all levels should also be derivable using the J-terms. We will show some of them in this section.

Identity context morphism is not a primitive notion in this framework. To define it, we have to declare all the properties it should hold as an identity morphism. In other words, substitution with identity morphism should keep everything unchanged.


\begin{code}
IdCm : ∀ Γ → Γ ⇒ Γ

IC-T  : ∀ {Γ : Con}(A : Ty Γ) → A [ IdCm Γ ]T ≡ A
IC-v  : ∀{Γ : Con}{A : Ty Γ}(x : Var A) →  x [ IdCm Γ ]V ≅ var x
IC-⊚  : ∀{Γ Δ : Con}(δ : Γ ⇒ Δ) → δ ⊚ IdCm Γ ≡ δ
IC-tm : ∀{Γ : Con}{A : Ty Γ}(a : Tm A) → a [ IdCm Γ ]tm ≅ a
\end{code}

\AgdaHide{
\begin{code}
IdCm ε = •
IdCm (Γ , A) = ((IdCm Γ) +S A) , wk-tm+ A (var v0 ⟦ wk-T (IC-T A) ⟫)

IC-T {Γ} * = refl
IC-T {Γ} (a =h b) = hom≡ (IC-tm a) (IC-tm b)

IC-v {.(Γ , A)} {.(A +T A)} (v0 {Γ} {A}) = wk-coh ∾ wk-coh+ ∾ cohOp (wk-T (IC-T A))

IC-v {.(Γ , B)} {.(A +T B)} (vS {Γ} {A} {B} x) = wk-coh ∾ [+S]V x ∾ cong+tm (IC-v x)

IC-⊚ • = refl
IC-⊚ {Γ} (_,_ δ {A} a) = cm-eq (IC-⊚ δ) (cohOp [⊚]T ∾ IC-tm a) 

IC-tm {Γ} {A} (var x) = IC-v x

IC-tm {Γ} {.(A [ δ ]T)} (JJ x δ A) = cohOp (sym [⊚]T) ∾ JJ-eq (IC-⊚ δ)


p1 : ∀ {Γ A} → (Γ , A) ⇒ Γ
p1 = IdCm _ +S _

p2 : ∀ {Γ A} → Tm {Γ , A} (A [ p1 ]T)
p2 = var v0 ⟦ trans [+S]T (wk-T (IC-T _)) ⟫

p2-v0 : ∀ {Γ A} → p2 {Γ} {A} ≅ var v0
p2-v0 {A = A} = cohOp (trans [+S]T (wk-T (IC-T A)))

Con-eq : {Γ Δ : Con}{A : Ty Γ}{B : Ty Δ} → (eq : Γ ≡ Δ) → subst Ty eq A ≡ B → _≡_ {_} {Con} (Γ , A) (Δ , B)
Con-eq refl refl = refl

\end{code}
}