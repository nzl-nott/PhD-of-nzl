{-# OPTIONS --no-positivity-check --no-termination-check #-}

open import GlobularSets



module Semantics (G : Glob)  where

open import Syntax
open import Data.Unit
open import Data.Product
open import Coinduction
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality as ht using (≅-to-≡) renaming (_≅_ to _≋_; refl to hrefl)


Eqhomo : ∀ {A A' u u' v v'} → A ≡ A' → u ≋ u' → v ≋ v' →  homo A u v ≋ homo A' u' v'
Eqhomo {.∣_∣ ∣∣ .homo} {∣_∣ ∣∣ homo} refl hrefl hrefl = hrefl

⟦_⟧C : Con → Set
⟦_⟧cm : ∀{Γ Δ : Con} → (Γ ⇒ Δ) → ⟦ Γ ⟧C → ⟦ Δ ⟧C
⟦_⟧T : ∀{Γ}(A : Ty Γ)(γ : ⟦ Γ ⟧C) → Glob
⟦_⟧tm : ∀{Γ A}(v : Tm A)(γ :  ⟦ Γ ⟧C) → ∣ ⟦ A ⟧T γ ∣ 

postulate J : (Θ : Con)(ic : isContr Θ)(A : Ty Θ) → (θ : ⟦ Θ ⟧C) → ∣ ⟦ A ⟧T θ ∣

⟦ ε ⟧C = ⊤
⟦ Γ , A ⟧C = Σ ⟦ Γ ⟧C (λ γ → ∣ ⟦ A ⟧T γ ∣)


⟦ * ⟧T γ = G
⟦ hom {A} u v ⟧T γ = ♭ (homo (⟦ A ⟧T γ) (⟦ u ⟧tm γ) (⟦ v ⟧tm γ))

--semantic weakening 

semWK-ty : ∀ {Γ : Con}(A : Ty Γ)(B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣) → ⟦ A ⟧T γ ≡ ⟦ A +T B ⟧T (γ , v)


semWK-tm : ∀ {Γ : Con}(A : Ty Γ)(B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)(a : Tm A) → ⟦ a ⟧tm γ ≋ ⟦ a +tm B ⟧tm (γ , v)


semWK-ty * B γ v = refl
semWK-ty (hom {A} a b) B γ v = cong ♭ (≅-to-≡ (Eqhomo (semWK-ty A B γ v) (semWK-tm _ _ _ _ a) (semWK-tm _ _ _ _ b)))

-- lemma 11
π : {Γ : Con}{A : Ty Γ}(x : Var A)(γ : ⟦ Γ ⟧C) → ∣ ⟦ A ⟧T γ ∣
π {.(Γ , A)} {.(A +T A)} (v0 {Γ} {A}) (γ , v) = subst ∣_∣ (semWK-ty A A γ v) v
π {.(Γ , B)} {.(A +T B)} (vS {Γ} {A} x {B}) (γ , v) = subst ∣_∣ (semWK-ty A B γ v) (π x γ)


{- we hav π so no need ⟦_⟧V
⟦ v0 {Γ} {A} ⟧V (γ , v) = semWK A A γ {!!} {!!} -- transport ws v -- ws v -- ⟦ vs u ⟧V {!!}
⟦ vS u ⟧V (γ , v) = {!!} -- transport ws (⟦ u ⟧V γ)
-}

lemTm : ∀ {Γ Δ}{A : Ty Δ}(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C) (a : Tm A) → ⟦ a ⟧tm (⟦ δ ⟧cm γ) ≋ ⟦ a [ δ ]tm ⟧tm γ


lemTy : ∀ {Γ Δ}{A : Ty Δ}(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C) → ⟦ A ⟧T (⟦ δ ⟧cm γ) ≡ ⟦ A [ δ ]T ⟧T γ
lemTy {Γ} {Δ} {*} δ γ = refl
lemTy {Γ} {Δ} {hom {A} a b} δ γ = cong ♭ (≅-to-≡ (Eqhomo (lemTy {A = A} δ γ) (lemTm _ _ a) (lemTm _ _ b)))

⟦_⟧tm (var x) γ = π x γ
⟦_⟧tm {Γ} (JJ {Δ = Δ} x δ A) γ = subst (λ x₁ → ∣ x₁ ∣) (lemTy {A = A} δ γ) (J Δ x A (⟦ δ ⟧cm γ))

cong≅-≋ : ∀{Γ : Con}{A B : Ty Γ}{x : Tm A}{y : Tm B}(G : Glob)(P : (ty : Ty Γ) → Tm ty → ∣ ⟦ ty ⟧T  ∣) → x ≅ y → P A x ≋ P B y
cong≅-≋ B P p = {!!}

semWK-tm Γ₁ A B γ (var x) = ht.sym (ht.≡-subst-removable ∣_∣ (semWK-ty Γ₁ A B γ) (π x B))
semWK-tm .(A₁ [ δ ]T) A γ a (JJ {Δ = Δ} x δ A₁) = 
  ht.trans (ht.≡-subst-removable ∣_∣ (lemTy {A = A₁} δ γ) ((J Δ x A₁ (⟦ δ ⟧cm γ)))) 
    (ht.sym (ht.trans (cong≅-≋ (⟦ (A₁ [ δ ]T) +T A ⟧T (γ , a)) (λ ty t → ⟦ {!y!} ⟧tm (γ , a)) {!!}) {! ⟦ JJ x (δ +S A) A₁ ⟦ [+S]T A₁ δ A ⟫ ⟧tm (γ , a) !}))

lemTm δ γ (var x) = {!x!}
lemTm δ γ (JJ x δ₁ A) = {!!}

⟦ • ⟧cm γ = tt
⟦ _,_ f {A} a ⟧cm γ = (⟦ f ⟧cm γ) , subst (λ x → ∣ x ∣) (sym (lemTy {A = A} f γ)) (⟦ a ⟧tm γ)
