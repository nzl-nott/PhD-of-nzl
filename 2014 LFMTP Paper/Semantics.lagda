
\AgdaHide{

\begin{code}
{-# OPTIONS --no-positivity-check --no-termination-check #-}




module Semantics where

open import BasicSyntax
open import IdentityContextMorphisms
open import Data.Unit
open import Data.Product
open import Coinduction
open import Relation.Binary.PropositionalEquality hiding ([_])
open import GroupoidStructure

open import GlobularTypes


coerce : {A B : Set} → B ≡ A → A → B
coerce refl a = a

⊤-uni : ∀ {A : Set}{a b : A} → A ≡ ⊤ → a ≡ b
⊤-uni refl = refl

\end{code}
}
Given a globular type $G$, we can interpret the syntactic objects.

\begin{code}
record Semantic (G : Glob) : Set₁ where
  field
    ⟦_⟧C  : Con → Set
    ⟦_⟧T  : ∀{Γ} → Ty Γ → ⟦ Γ ⟧C → Glob
    ⟦_⟧tm : ∀{Γ A} → Tm A → (γ : ⟦ Γ ⟧C) → ∣ ⟦ A ⟧T γ ∣
    ⟦_⟧cm : ∀{Γ Δ} → Γ ⇒ Δ → ⟦ Γ ⟧C → ⟦ Δ ⟧C
    π     : ∀{Γ A} → Var A → (γ : ⟦ Γ ⟧C) → ∣ ⟦ A ⟧T γ ∣
\end{code}
$\AgdaField{π}$ provides the projection of the semantic variable out of a semantic context.

Following are the computation laws for the interpretations of contexts and types.

\begin{code}
    ⟦_⟧C-β1  : ⟦ ε ⟧C ≡ ⊤
    ⟦_⟧C-β2  : ∀ {Γ A} → ⟦ Γ , A ⟧C ≡ 
                         Σ ⟦ Γ ⟧C (λ γ  → ∣ ⟦ A ⟧T γ ∣)
    
    ⟦_⟧T-β1  : ∀{Γ}{γ : ⟦ Γ ⟧C} → ⟦ * ⟧T γ ≡ G
    ⟦_⟧T-β2  : ∀{Γ A u v}{γ : ⟦ Γ ⟧C}
             → ⟦ u =h v ⟧T γ ≡
               ♭ (hom (⟦ A ⟧T γ) (⟦ u ⟧tm γ) (⟦ v ⟧tm γ))
\end{code}
Semantic substitution and semantic weakening laws are also required.
The semantic substitution properties are essential for dealing with substitutions inside interpretation,

\begin{code}
    semSb-T  : ∀ {Γ Δ}(A : Ty Δ)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C)
             → ⟦ A [ δ ]T ⟧T γ ≡ ⟦ A ⟧T (⟦ δ ⟧cm γ)

    semSb-tm : ∀{Γ Δ}{A : Ty Δ}(a : Tm A)(δ : Γ ⇒ Δ)
               (γ : ⟦ Γ ⟧C)
             → subst ∣_∣ (semSb-T A δ γ) (⟦ a [ δ ]tm ⟧tm γ)
                ≡ ⟦ a ⟧tm (⟦ δ ⟧cm γ)

    semSb-cm : ∀ {Γ Δ Θ}(γ : ⟦ Γ ⟧C)(δ : Γ ⇒ Δ)(θ : Δ ⇒ Θ)
             → ⟦ θ ⊚ δ ⟧cm γ ≡ ⟦ θ ⟧cm (⟦ δ ⟧cm γ)
\end{code}
Since the computation laws for the interpretations of terms and context morphisms are well typed up to these properties.

\begin{code}
    ⟦_⟧tm-β1  : ∀{Γ A}{x : Var A}{γ : ⟦ Γ ⟧C}
              → ⟦ var x ⟧tm γ ≡ π x γ

    ⟦_⟧cm-β1  : ∀{Γ}{γ : ⟦ Γ ⟧C} 
             → ⟦ • ⟧cm γ ≡ coerce ⟦_⟧C-β1 tt

    ⟦_⟧cm-β2  : ∀{Γ Δ}{A : Ty Δ}{δ : Γ ⇒ Δ}{γ : ⟦ Γ ⟧C}
                {a : Tm (A [ δ ]T)} → ⟦ δ , a ⟧cm γ 
              ≡ coerce ⟦_⟧C-β2 ((⟦ δ ⟧cm γ) ,
                subst ∣_∣ (semSb-T A δ γ) (⟦ a ⟧tm γ))
\end{code}
The semantic weakening properties should actually be deriavable since weakening is equivalent to projection substitution.

\begin{code}
    semWk-T  : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
             → ⟦ A +T B ⟧T (coerce ⟦_⟧C-β2 (γ , v)) ≡ 
               ⟦ A ⟧T γ
  
    semWk-cm  : ∀ {Γ Δ B}{γ : ⟦ Γ ⟧C}{v : ∣ ⟦ B ⟧T γ ∣}
              → (δ : Γ ⇒ Δ) → ⟦ δ +S B ⟧cm 
                (coerce ⟦_⟧C-β2 (γ , v)) ≡ ⟦ δ ⟧cm γ


    semWk-tm : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
             → (a : Tm A) → subst ∣_∣ (semWk-T γ v) 
               (⟦ a +tm B ⟧tm (coerce ⟦_⟧C-β2 (γ , v))) 
                 ≡ (⟦ a ⟧tm γ)
\end{code}
Here we declare them as properties because they are essential for the computation laws of function $\AgdaField{π}$.

\begin{code}
    π-β1  : ∀{Γ A}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ A ⟧T γ ∣) 
          → subst ∣_∣ (semWk-T γ v) 
            (π v0 (coerce ⟦_⟧C-β2 (γ , v))) ≡ v

    π-β2  : ∀{Γ A B}(x : Var A)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣) 
          → subst ∣_∣ (semWk-T γ v) (π (vS {Γ} {A} {B} x) 
            (coerce ⟦_⟧C-β2 (γ , v))) ≡ π x γ
\end{code}
The only part of the semantics where we have any freedom is the interpretation of the coherence constants:

\begin{code}
    ⟦coh⟧  : ∀{Θ} → isContr Θ → (A : Ty Θ) 
           → (θ : ⟦ Θ ⟧C) → ∣ ⟦ A ⟧T θ ∣
\end{code}
However, we also need to require that the coherence constants are well
behaved wrt to substitution which in turn relies on the interpretation
of all terms. To address this we state the required properties in a
redundant form because the correctness for any other part of the
syntax follows from the defining equations we have already
stated. There seems to be no way to avoid this.

If the underlying globular type is not a globular set we need to add coherence laws, which is not very well understood. On the other hand, restricting ourselves to globular sets means that our prime examle $\AgdaFunction{Idω}$ is not an instance anymore. We should still be able to construct non-trivial globular sets, e.g. by encoding basic topological notions and defining higher homotopies as in a classical framework. However, we don't currently know a simple definition of a globular set which is a weak $\omega$-groupoid. One possibility would be to use the syntax of type theory with equality types. Indeed, we believe that this would be an alternative way to formalize weak $\omega$-groupoids.
