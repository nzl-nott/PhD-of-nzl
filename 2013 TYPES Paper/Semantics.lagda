
\AgdaHide{

\begin{code}
{-# OPTIONS --no-positivity-check --no-termination-check #-}

open import GlobularSets



module Semantics where

open import AIOOG
open import Data.Unit
open import Data.Product
open import Coinduction
open import Relation.Binary.PropositionalEquality hiding ([_])
open import GroupoidLaws
\end{code}
}

given a globular set G, we could interpret the objects in syntactic frameworks.

The record definition also require some semantic weakening and semantic substitution laws. The semantic weakening rules tell us how to deal with the weakening inside interpretation.


\begin{code}
record Semantic (G : Glob) : Set₁ where
  field
    ⟦_⟧C  : Con → Set
    ⟦_⟧T  : ∀{Γ} → Ty Γ → ⟦ Γ ⟧C → Glob
    ⟦_⟧tm : ∀{Γ A} → Tm A → (γ : ⟦ Γ ⟧C) → ∣ ⟦ A ⟧T γ ∣
    ⟦_⟧cm : ∀{Γ Δ} → Γ ⇒ Δ → ⟦ Γ ⟧C → ⟦ Δ ⟧C
\end{code}
To interpret the coherence constants we need a function $\AgdaFunction{⟦coh⟧}$ \footnote{it is called J in Brunerie's note but to make it less ambiguous we renamed it}. It returns an object for every type in any contractible context, namely what is called a valid coherence in Brunerie's paper. 
\begin{code}
    ⟦coh⟧ : ∀{Θ} → isContr Θ → (A : Ty Θ) → (θ : ⟦ Θ ⟧C) → ∣ ⟦ A ⟧T θ ∣
\end{code}

$\AgdaFunction{$\pi$}$ gives us a simpler way to project the semantic meaning of certain variable out of a context.

\begin{code}
    π     : ∀{Γ A}(x : Var A)(γ : ⟦ Γ ⟧C) → ∣ ⟦ A ⟧T γ ∣
\end{code}

Following are the computation laws for the interpretations of contexts and types.

\begin{code}
    sC-b1 : ⟦ ε ⟧C ≡ ⊤
    sC-b2 : ∀ {Γ A} → ⟦ Γ , A ⟧C ≡ Σ ⟦ Γ ⟧C (λ γ  → ∣ ⟦ A ⟧T γ ∣)
    
    sT-b1 : ∀{Γ}{γ : ⟦ Γ ⟧C} → ⟦ * ⟧T γ ≡ G
    sT-b2 : ∀{Γ A u v}{γ : ⟦ Γ ⟧C} → 
            ⟦ u =h v ⟧T γ ≡
            ♭ (hom (⟦ A ⟧T γ) (⟦ u ⟧tm γ) (⟦ v ⟧tm γ))
\end{code}

The computation laws of terms and context morphisms are well typed with the semantic substitution lemmas.

\begin{code}
    semSB-T : ∀ {Γ Δ}(A : Ty Δ)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C)
            → ⟦ A [ δ ]T ⟧T γ ≡ ⟦ A ⟧T (⟦ δ ⟧cm γ)
    
    stm-b1 : ∀{Γ A}{x : Var A}{γ : ⟦ Γ ⟧C}
           → ⟦ var x ⟧tm γ ≡ π x γ
    stm-b2 : ∀{Γ Δ x δ}{A : Ty Δ}{γ : ⟦ Γ ⟧C}
           → subst ∣_∣ (semSB-T A δ γ) (⟦ coh x δ A ⟧tm γ) ≡ ⟦coh⟧ x A (⟦ δ ⟧cm γ)

    scm-b1 : ∀{Γ}{γ : ⟦ Γ ⟧C} → ⟦ • ⟧cm γ ≡ subst (λ x → x) (sym sC-b1) tt
    scm-b2 : ∀{Γ Δ}{A : Ty Δ}{δ : Γ ⇒ Δ}{γ : ⟦ Γ ⟧C}{a : Tm (A [ δ ]T)}
           → ⟦ δ , a ⟧cm γ ≡ subst (λ x → x) (sym sC-b2) ((⟦ δ ⟧cm γ) ,
                            subst (λ x → ∣ x ∣) (semSB-T A δ γ) (⟦ a ⟧tm γ))
\end{code}
The semantic weakening lemmas is also essential,
\begin{code}
    semWK-T : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
            → ⟦ A ⟧T γ 
              ≡ ⟦ A +T B ⟧T (subst (λ x → x) (sym sC-b2) (γ , v))

    semWK-tm : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)
               (v : ∣ ⟦ B ⟧T γ ∣)(a : Tm A)
             → subst ∣_∣ (semWK-T γ v) (⟦ a ⟧tm γ)
               ≡ ⟦ a +tm B ⟧tm (subst (λ x → x) (sym sC-b2) (γ , v))

    semWK-cm : ∀ {Γ Δ B}(γ : ⟦ Γ ⟧C)
                 (v : ∣ ⟦ B ⟧T γ ∣)(δ : Γ ⇒ Δ)
             → ⟦ δ ⟧cm γ ≡ ⟦ δ +S B ⟧cm (subst (λ x → x) (sym sC-b2) (γ , v))
\end{code}
so that the following computation laws of projection function $\AgdaFunction{$\pi$}$ and coherence function $\AgdaFunction{⟦coh⟧}$ is well typed.
\begin{code}
    π-b1 : ∀{Γ A}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ A ⟧T γ ∣) 
         → π v0 (subst (λ x → x) (sym sC-b2) (γ , v)) 
           ≡ subst ∣_∣ (semWK-T γ v) v
    π-b2 : ∀{Γ A B}(x : Var A)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣) 
         → π (vS {Γ} {A} {B} x) (subst (λ y → y) (sym sC-b2) (γ , v)) 
           ≡ subst ∣_∣ (semWK-T γ v) (π x γ)

    coh-b1 : ∀{Γ : Con}(A B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
               (ic : isContr Γ)(ic' : isContr (Γ , B))
           → subst ∣_∣ (semWK-T γ v) (⟦coh⟧ ic A γ) ≡ 
             ⟦coh⟧ ic' (A +T B) (subst (λ x → x) (sym sC-b2) (γ , v))
\end{code}
At last, the semantic substitution lemmas for terms, context morphisms.
\begin{code}
    semSB-tm : ∀{Γ Δ}{A : Ty Δ}(a : Tm A)
                 (δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C)
             → subst ∣_∣ (semSB-T A δ γ) (⟦ a [ δ ]tm ⟧tm γ) ≡ ⟦ a ⟧tm (⟦ δ ⟧cm γ)

    semSB-cm : ∀ {Γ Δ Θ}(γ : ⟦ Γ ⟧C)
               (δ : Γ ⇒ Δ)(θ : Δ ⇒ Θ)
             → ⟦ θ ⊚ δ ⟧cm γ ≡ ⟦ θ ⟧cm (⟦ δ ⟧cm γ)
\end{code}

We don't know whether we should more coherence laws for thesse interpretations.

\AgdaHide{

\begin{code}

{-
Id-tm : {Γ : Con}{A : Ty Γ}(t : Tm A)(γ : ⟦ Γ ⟧C) → ∣ ⟦ Tm-refl _ _ t ⟧tm γ ∣
Id-tm t γ = {!γ!}

R : (θ : Con)(isC : isContr θ) → ⟦ ε , * ⟧C → ⟦ θ ⟧C
R .(ε , *) c* t = t
R .(Γ , A , (var (vS x) =h var v0)) (ext {Γ} isC {A} x) (tt , g) = (R Γ isC (tt , g) , ⟦ var x ⟧tm (R Γ isC (tt , g))) , {!!} -- ⟦ Tm-refl _ _ (var x) ⟧tm {!!} -- {!!} , {!!}
-}

\end{code}
}