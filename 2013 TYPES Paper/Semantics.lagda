
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

given a globular set G, we could interpret the objects in syntactic frameworks. To interpret the Coherence terms (JJ-terms) we need a function \emph{Coh} \footnote{it was called J in Brunerie's note but to make it less ambiguous we renamed it}. It returns an object for every type in any contractible context, namely what is called a valid coherence in Brunerie's paper. 

The record definition also require some semantic weakening and semantic substitution laws. The semantic weakening rules tell us how to deal with the weakening inside interpretation.


\begin{code}
record Semantic (G : Glob) : Set₁ where
  field
    ⟦_⟧C : Con → Set
    ⟦_⟧cm : ∀{Γ Δ : Con} → (Γ ⇒ Δ) → ⟦ Γ ⟧C → ⟦ Δ ⟧C
    ⟦_⟧T : ∀{Γ}(A : Ty Γ)(γ : ⟦ Γ ⟧C) → Glob
    ⟦_⟧tm : ∀{Γ A}(v : Tm A)(γ :  ⟦ Γ ⟧C) → ∣ ⟦ A ⟧T γ ∣ 
    Coh : (Θ : Con)(ic : isContr Θ)(A : Ty Θ) → (θ : ⟦ Θ ⟧C) → ∣ ⟦ A ⟧T θ ∣
    π : {Γ : Con}{A : Ty Γ}(x : Var A)(γ : ⟦ Γ ⟧C) → ∣ ⟦ A ⟧T γ ∣

    sC-b1 : ⟦ ε ⟧C ≡ ⊤
    sC-b2 : ∀ {Γ A} → ⟦ Γ , A ⟧C ≡ Σ ⟦ Γ ⟧C (λ γ  → ∣ ⟦ A ⟧T γ ∣)
    
    sT-b1 : ∀{Γ}{γ : ⟦ Γ ⟧C} → ⟦ * ⟧T γ ≡ G
    sT-b2 : ∀{Γ}{A}{u v}{γ : ⟦ Γ ⟧C} → 
            ⟦ u =h v ⟧T γ ≡
            ♭ (hom (⟦ A ⟧T γ) (⟦ u ⟧tm γ) (⟦ v ⟧tm γ))


    lemTy : ∀ {Γ Δ}(A : Ty Δ)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C) → 
            ⟦ A ⟧T (⟦ δ ⟧cm γ) ≡
            ⟦ A [ δ ]T ⟧T γ

    stm-b1 : ∀{Γ}{A}{x : Var A}{γ : ⟦ Γ ⟧C} → 
             ⟦ var x ⟧tm γ ≡ π x γ
    stm-b2 : ∀{Γ Δ A x δ}{γ : ⟦ Γ ⟧C} →
             ⟦ JJ x δ A ⟧tm γ ≡ subst ∣_∣ (lemTy A δ γ) (Coh Δ x A (⟦ δ ⟧cm γ))

    scm-b1 : ∀{Γ}{γ : ⟦ Γ ⟧C} → ⟦ • ⟧cm γ ≡ subst (λ x → x) (sym sC-b1) tt
    scm-b2 : ∀{Γ Δ}{A : Ty Δ}{δ : Γ ⇒ Δ}{γ : ⟦ Γ ⟧C}{a : Tm (A [ δ ]T)} → ⟦ _,_ δ a ⟧cm γ ≡ 
             subst (λ x → x) (sym sC-b2) ((⟦ δ ⟧cm γ) , 
             subst (λ x → ∣ x ∣) (sym (lemTy A δ γ)) (⟦ a ⟧tm γ))

    lemTm : ∀ {Γ Δ}(A : Ty Δ)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C) (a : Tm A) → 
            subst ∣_∣ (lemTy A δ γ) (⟦ a ⟧tm (⟦ δ ⟧cm γ)) ≡
            ⟦ a [ δ ]tm ⟧tm γ
  
    
    semWK-ty : ∀ {Γ : Con}(A B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣) 
             → ⟦ A ⟧T γ ≡ ⟦ A +T B ⟧T (subst (λ x → x) (sym sC-b2) (γ , v))

    semWK-tm : ∀ {Γ : Con}(A B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
                 (a : Tm A) → subst ∣_∣ (semWK-ty A B γ v) (⟦ a ⟧tm γ) 
                        ≡ ⟦ a +tm B ⟧tm (subst (λ x → x) (sym sC-b2) (γ , v))

    semWK-cm : ∀ {Γ Δ : Con}(B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
                 (δ : Γ ⇒ Δ) → ⟦ δ ⟧cm γ ≡ 
                 ⟦ δ +S B ⟧cm (subst (λ x → x) (sym sC-b2) (γ , v))


    π-b1 : ∀{Γ A}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ A ⟧T γ ∣) → π (v0 {Γ} {A}) (subst (λ x → x) (sym sC-b2) (γ , v)) ≡ subst ∣_∣ (semWK-ty A A γ v) v
    π-b2 : ∀{Γ A B}(x : Var A)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣) → π (vS {Γ} {A} {B} x) (subst (λ y → y) (sym sC-b2) (γ , v)) ≡ subst ∣_∣ (semWK-ty A B γ v) (π x γ)

    coh-comm : ∀ {Γ : Con}(A B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
                 (ic : isContr Γ)(ic' : isContr (Γ , B))
                 → subst ∣_∣ (semWK-ty A B γ v) (Coh Γ ic A γ) ≡ 
                 Coh (Γ , B) ic' (A +T B) (subst (λ x → x) (sym sC-b2) (γ , v))

    
    semSB-ty : ∀ {Γ Δ : Con}(A : Ty Δ)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C)
             → ⟦ A [ δ ]T ⟧T γ ≡ ⟦ A ⟧T (⟦ δ ⟧cm γ)
    
    semSB-tm : ∀ {Γ Δ : Con}{A : Ty Δ}(a : Tm A)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C)
             → subst ∣_∣ (semSB-ty A δ γ) (⟦ a [ δ ]tm ⟧tm γ) ≡ ⟦ a ⟧tm (⟦ δ ⟧cm γ)
    
    semSB-cm : ∀ {Γ Δ Θ : Con}(γ : ⟦ Γ ⟧C)(δ : Γ ⇒ Δ)(θ : Δ ⇒ Θ)
             → ⟦ θ ⊚ δ ⟧cm γ ≡ ⟦ θ ⟧cm (⟦ δ ⟧cm γ)

\end{code}



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