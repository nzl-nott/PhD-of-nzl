
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

\textbf{Semantic interpretation}

\begin{code}
record Semantic (G : Glob) : Set₁ where
  field
    ⟦_⟧C   : Con → Set
    ⟦_⟧T   : ∀{Γ} → Ty Γ → ⟦ Γ ⟧C → Glob
    ⟦_⟧tm  : ∀{Γ A} → Tm A → (γ : ⟦ Γ ⟧C) 
           → ∣ ⟦ A ⟧T γ ∣
    ⟦_⟧S   : ∀{Γ Δ} → Γ ⇒ Δ → ⟦ Γ ⟧C → ⟦ Δ ⟧C
    π      : ∀{Γ A} → Var A → (γ : ⟦ Γ ⟧C) 
           → ∣ ⟦ A ⟧T γ ∣
    ⟦_⟧C-β1  : ⟦ ε ⟧C ≡ ⊤
    ⟦_⟧C-β2  : ∀ {Γ A} → ⟦ Γ , A ⟧C ≡ 
             Σ ⟦ Γ ⟧C (λ γ  → ∣ ⟦ A ⟧T γ ∣)
    
    ⟦_⟧T-β1  : ∀{Γ}{γ : ⟦ Γ ⟧C} → ⟦ * ⟧T γ ≡ G
    ⟦_⟧T-β2  : ∀{Γ A u v}{γ : ⟦ Γ ⟧C}
             → ⟦ u =h v ⟧T γ ≡
             ♭ (hom (⟦ A ⟧T γ) (⟦ u ⟧tm γ) (⟦ v ⟧tm γ))

    semSb-T   : ∀ {Γ Δ}(A : Ty Δ)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C)
              → ⟦ A [ δ ]T ⟧T γ ≡ ⟦ A ⟧T (⟦ δ ⟧S γ)

    semSb-tm  : ∀{Γ Δ}{A : Ty Δ}(a : Tm A)(δ : Γ ⇒ Δ)
              (γ : ⟦ Γ ⟧C) → subst ∣_∣ (semSb-T A δ γ) 
              (⟦ a [ δ ]tm ⟧tm γ) ≡ ⟦ a ⟧tm (⟦ δ ⟧S γ)

    semSb-S   : ∀ {Γ Δ Θ}(γ : ⟦ Γ ⟧C)(δ : Γ ⇒ Δ)
              (θ : Δ ⇒ Θ) → ⟦ θ ⊚ δ ⟧S γ ≡ 
              ⟦ θ ⟧S (⟦ δ ⟧S γ)

    ⟦_⟧tm-β1  : ∀{Γ A}{x : Var A}{γ : ⟦ Γ ⟧C}
              → ⟦ var x ⟧tm γ ≡ π x γ

    ⟦_⟧S-β1  : ∀{Γ}{γ : ⟦ Γ ⟧C} 
             → ⟦ • ⟧S γ ≡ coerce ⟦_⟧C-β1 tt

    ⟦_⟧S-β2  : ∀{Γ Δ}{A : Ty Δ}{δ : Γ ⇒ Δ}{γ : ⟦ Γ ⟧C}
             {a : Tm (A [ δ ]T)} → ⟦ δ , a ⟧S γ 
             ≡ coerce ⟦_⟧C-β2 ((⟦ δ ⟧S γ) ,
             subst ∣_∣ (semSb-T A δ γ) (⟦ a ⟧tm γ))

    semWk-T  : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
             → ⟦ A +T B ⟧T (coerce ⟦_⟧C-β2 (γ , v)) ≡ 
             ⟦ A ⟧T γ
  

    semWk-S  : ∀ {Γ Δ B}{γ : ⟦ Γ ⟧C}{v : ∣ ⟦ B ⟧T γ ∣}
             → (δ : Γ ⇒ Δ) → ⟦ δ +S B ⟧S 
             (coerce ⟦_⟧C-β2 (γ , v)) ≡ ⟦ δ ⟧S γ

    semWk-tm : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
             → (a : Tm A) → subst ∣_∣ (semWk-T γ v) 
               (⟦ a +tm B ⟧tm (coerce ⟦_⟧C-β2 (γ , v))) 
                 ≡ (⟦ a ⟧tm γ)

    π-β1  : ∀{Γ A}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ A ⟧T γ ∣) 
          → subst ∣_∣ (semWk-T γ v) 
            (π v0 (coerce ⟦_⟧C-β2 (γ , v))) ≡ v

    π-β2  : ∀{Γ A B}(x : Var A)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣) 
          → subst ∣_∣ (semWk-T γ v) (π (vS {Γ} {A} {B} x) 
            (coerce ⟦_⟧C-β2 (γ , v))) ≡ π x γ

    ⟦coh⟧  : ∀{Θ} → isContr Θ → (A : Ty Θ) 
           → (θ : ⟦ Θ ⟧C) → ∣ ⟦ A ⟧T θ ∣
\end{code}
