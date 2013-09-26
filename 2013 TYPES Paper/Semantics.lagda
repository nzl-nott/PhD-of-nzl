
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

Given a globular set G, we can interpret the syntactic objects.

The record definition also require some semantic weakening and semantic substitution laws. The semantic weakening rules tell us how to deal with the weakening inside interpretation.


\begin{code}
record Semantic (G : Glob) : Set₁ where
  field
    ⟦_⟧C   : Con → Set
    ⟦_⟧T   : ∀{Γ} → Ty Γ → ⟦ Γ ⟧C → Glob
    ⟦_⟧tm  : ∀{Γ A} → Tm A → (γ : ⟦ Γ ⟧C) → ∣ ⟦ A ⟧T γ ∣
    ⟦_⟧cm  : ∀{Γ Δ} → Γ ⇒ Δ → ⟦ Γ ⟧C → ⟦ Δ ⟧C
\end{code}
To interpret the coherence constants we need a function $\AgdaFunction{⟦coh⟧}$ \footnote{it is called J in Brunerie's note but to make it less ambiguous we renamed it.}. It returns an object for every type in any contractible context, namely what is called a valid coherence in Brunerie's paper. 
\begin{code}
    ⟦coh⟧ : ∀{Θ} → isContr Θ → (A : Ty Θ) → (θ : ⟦ Θ ⟧C) → ∣ ⟦ A ⟧T θ ∣
\end{code}

$\AgdaFunction{$\pi$}$ gives us a simpler way to project the semantic meaning of certain variable out of a context.

\begin{code}
    π     : ∀{Γ A}(x : Var A)(γ : ⟦ Γ ⟧C) → ∣ ⟦ A ⟧T γ ∣
\end{code}

Following are the computation laws for the interpretations of contexts and types.

\begin{code}
    sC-β1 : ⟦ ε ⟧C ≡ ⊤
    sC-β2 : ∀ {Γ A} → ⟦ Γ , A ⟧C ≡ Σ ⟦ Γ ⟧C (λ γ  → ∣ ⟦ A ⟧T γ ∣)
    
    sT-β1  : ∀{Γ}{γ : ⟦ Γ ⟧C} → ⟦ * ⟧T γ ≡ G
    sT-β2  : ∀{Γ A u v}{γ : ⟦ Γ ⟧C}
           → ⟦ u =h v ⟧T γ ≡
             ♭ (hom (⟦ A ⟧T γ) (⟦ u ⟧tm γ) (⟦ v ⟧tm γ))
\end{code}

The computation laws of terms and context morphisms are well typed with the semantic substitution lemmas.

\begin{code}
    semSb-T  : ∀ {Γ Δ}(A : Ty Δ)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C)
             → ⟦ A [ δ ]T ⟧T γ ≡ ⟦ A ⟧T (⟦ δ ⟧cm γ)
    
    stm-β1  : ∀{Γ A}{x : Var A}{γ : ⟦ Γ ⟧C}
            → ⟦ var x ⟧tm γ ≡ π x γ
    stm-β2  : ∀{Γ Δ x δ}{A : Ty Δ}{γ : ⟦ Γ ⟧C}
            → subst ∣_∣ (semSb-T A δ γ) (⟦ coh x δ A ⟧tm γ) 
              ≡ ⟦coh⟧ x A (⟦ δ ⟧cm γ)

    scm-β1  : ∀{Γ}{γ : ⟦ Γ ⟧C} → ⟦ • ⟧cm γ ≡ subst (λ x → x) (sym sC-β1) tt
    scm-β2  : ∀{Γ Δ}{A : Ty Δ}{δ : Γ ⇒ Δ}{γ : ⟦ Γ ⟧C}{a : Tm (A [ δ ]T)}
            → ⟦ δ , a ⟧cm γ ≡ subst (λ x → x) (sym sC-β2) ((⟦ δ ⟧cm γ) ,
                             subst ∣_∣ (semSb-T A δ γ) (⟦ a ⟧tm γ))
\end{code}
The semantic weakening lemmas is also essential,
\begin{code}

    semWk-T : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
            → ⟦ A ⟧T γ ≡ ⟦ A +T B ⟧T 
                         (subst (λ x → x) (sym sC-β2) (γ , v))

    semWk-tm : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)(a : Tm A)
             → subst ∣_∣ (semWk-T γ v) (⟦ a ⟧tm γ) ≡ ⟦ a +tm B ⟧tm 
                           (subst (λ x → x) (sym sC-β2) (γ , v))

    semWk-cm : ∀ {Γ Δ B}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)(δ : Γ ⇒ Δ)
             → ⟦ δ ⟧cm γ ≡ ⟦ δ +S B ⟧cm
                        (subst (λ x → x) (sym sC-β2) (γ , v))

\end{code}
so that the following computation laws of projection function $\AgdaFunction{$\pi$}$ and coherence function $\AgdaFunction{⟦coh⟧}$ is well typed.

\begin{code}
    π-β1  : ∀{Γ A}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ A ⟧T γ ∣) 
          → π v0 (subst (λ x → x) (sym sC-β2) (γ , v)) 
           ≡ subst ∣_∣ (semWk-T γ v) v

    π-β2  : ∀{Γ A B}(x : Var A)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣) 
          → π (vS {Γ} {A} {B} x) (subst (λ y → y) (sym sC-β2) (γ , v)) 
           ≡ subst ∣_∣ (semWk-T γ v) (π x γ)

    coh-β1 : ∀{Γ : Con}(A B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
               (ic : isContr Γ)(ic' : isContr (Γ , B))
           → subst ∣_∣ (semWk-T γ v) (⟦coh⟧ ic A γ) ≡ 
             ⟦coh⟧ ic' (A +T B) (subst (λ x → x) (sym sC-β2) (γ , v))
\end{code}
At last, the semantic substitution lemmas for terms, context morphisms.

\begin{code}
    semSb-tm : ∀{Γ Δ}{A : Ty Δ}(a : Tm A)
                 (δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C)
             → subst ∣_∣ (semSb-T A δ γ) (⟦ a [ δ ]tm ⟧tm γ) ≡ ⟦ a ⟧tm (⟦ δ ⟧cm γ)

    semSb-cm : ∀ {Γ Δ Θ}(γ : ⟦ Γ ⟧C)
               (δ : Γ ⇒ Δ)(θ : Δ ⇒ Θ)
             → ⟦ θ ⊚ δ ⟧cm γ ≡ ⟦ θ ⟧cm (⟦ δ ⟧cm γ)
\end{code}

If the underlying globular type is not a globular set we need to add coherence laws, which is not very well understood. On the other hand, restricting ourselves to globular sets means that our prime examle |Idω| is not an instance anymore. We should still be able to construct non-trivial globular sets, e.g. by encoding basic topological notions and defining higher homotopies as in a classical framework. However, we don't currently know a simple definition of a globular set which is a weak $\omega$-groupoid. One possibility would be to use the syntax of type theory with equality types. Indeed, we believe that this would be an alternative way to formalize weak $\omega$-groupoids.

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