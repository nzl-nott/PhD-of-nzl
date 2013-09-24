
\AgdaHide{

\begin{code}
{-# OPTIONS --no-positivity-check --no-termination-check #-}

open import GlobularSets



module Semantics (G : Glob)  where

open import AIOOG
open import Data.Unit
open import Data.Product
open import Coinduction
open import Relation.Binary.PropositionalEquality hiding ([_])
open import GroupoidLaws


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
    sT-b2 : ∀{Γ}{A}{u v}{γ : ⟦ Γ ⟧C} → ⟦ u =h v ⟧T γ ≡ ♭ (hom (⟦ A ⟧T γ) (⟦ u ⟧tm γ) (⟦ v ⟧tm γ))

    lemTy : ∀ {Γ Δ}(A : Ty Δ)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C) → ⟦ A ⟧T (⟦ δ ⟧cm γ) ≡ ⟦ A [ δ ]T ⟧T γ

    stm-b1 : ∀{Γ}{A}{x : Var A}{γ : ⟦ Γ ⟧C} → ⟦ var x ⟧tm γ ≡ π x γ
    stm-b2 : ∀{Γ Δ A x δ}{γ : ⟦ Γ ⟧C} → ⟦ JJ x δ A ⟧tm γ ≡ subst ∣_∣ (lemTy A δ γ) (Coh Δ x A (⟦ δ ⟧cm γ))

    
    lemTm : ∀ {Γ Δ}(A : Ty Δ)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C) (a : Tm A) → subst ∣_∣ (lemTy A δ γ) (⟦ a ⟧tm (⟦ δ ⟧cm γ)) ≡ ⟦ a [ δ ]tm ⟧tm γ
  
    
    semWK-ty : ∀ {Γ : Con}(A B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣) 
             → ⟦ A ⟧T γ ≡ ⟦ A +T B ⟧T (subst (λ x → x) (sym sC-b2) (γ , v))

    semWK-tm : ∀ {Γ : Con}(A B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
                 (a : Tm A) → subst ∣_∣ (semWK-ty A B γ v) (⟦ a ⟧tm γ) 
                        ≡ ⟦ a +tm B ⟧tm (subst (λ x → x) (sym sC-b2) (γ , v))

    semWK-cm : ∀ {Γ Δ : Con}(B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
                 (δ : Γ ⇒ Δ) → ⟦ δ ⟧cm γ ≡ ⟦ δ +S B ⟧cm (subst (λ x → x) (sym sC-b2) (γ , v))


    coh-comm : ∀ {Γ : Con}(A B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)(ic : isContr Γ)(ic' : isContr (Γ , B))
                 → subst ∣_∣ (semWK-ty A B γ v) (Coh Γ ic A γ) ≡ Coh (Γ , B) ic' (A +T B) (subst (λ x → x) (sym sC-b2) (γ , v))
\end{code}
}

Then given a globular set G, we could interpret the objects in syntactic frameworks. 

\begin{code}
⟦_⟧C : Con → Set
⟦_⟧cm : ∀{Γ Δ : Con} → (Γ ⇒ Δ) → ⟦ Γ ⟧C → ⟦ Δ ⟧C
⟦_⟧T : ∀{Γ}(A : Ty Γ)(γ : ⟦ Γ ⟧C) → Glob
⟦_⟧tm : ∀{Γ A}(v : Tm A)(γ :  ⟦ Γ ⟧C) → ∣ ⟦ A ⟧T γ ∣ 
\end{code}

Another necessary thing is a dependent function Coh \footnote{it was called J but to make it less ambiguous we renamed it} should also comes with the globular set. It returns an object for every type in any contractible context, namely what is called a valid coherence in Brunerie's paper. This actually enables us to interpret J-terms in syntax.

\begin{code}
Coh : (Θ : Con)(ic : isContr Θ)(A : Ty Θ) → (θ : ⟦ Θ ⟧C) → ∣ ⟦ A ⟧T θ ∣
\end{code}

We temporarily postulate $Coh$ function so that we could define the interpretations. However we would adopt the correct way later by defining a record type including the globular set, the interpretations and this function.

\AgdaHide{
\begin{code}

postulate Coh' : (Θ : Con)(ic : isContr Θ)(A : Ty Θ) → (θ : ⟦ Θ ⟧C) 
             → ∣ ⟦ A ⟧T θ ∣
Coh = Coh'

⟦ ε ⟧C = ⊤
⟦ Γ , A ⟧C = Σ ⟦ Γ ⟧C (λ γ → ∣ ⟦ A ⟧T γ ∣)


⟦ * ⟧T γ = G
⟦ _=h_ {A} u v ⟧T γ = ♭ (hom (⟦ A ⟧T γ) (⟦ u ⟧tm γ) (⟦ v ⟧tm γ))

\end{code}
}

There are also some lemmas for weakening to prove as before. The semantic weakening rules tell us how to deal with the weakening inside interpretation.

\begin{code}
semWK-ty : ∀ {Γ : Con}(A B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣) 
         → ⟦ A ⟧T γ ≡ ⟦ A +T B ⟧T (γ , v)

semWK-tm : ∀ {Γ : Con}(A B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
             (a : Tm A) → subst ∣_∣ (semWK-ty A B γ v) (⟦ a ⟧tm γ) 
                        ≡ ⟦ a +tm B ⟧tm (γ , v)

semWK-cm : ∀ {Γ Δ : Con}(B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
             (δ : Γ ⇒ Δ) → ⟦ δ ⟧cm γ ≡ ⟦ δ +S B ⟧cm (γ , v)
\end{code}

\AgdaHide{

\begin{code}

semWK-ty * B γ v = refl
semWK-ty (_=h_ {A} a b) B γ v = EqHom (semWK-ty A _ _ _) (semWK-tm _ _ _ _ a) (semWK-tm _ _ _ _ b)

-- lemma 11
π : {Γ : Con}{A : Ty Γ}(x : Var A)(γ : ⟦ Γ ⟧C) → ∣ ⟦ A ⟧T γ ∣
π {.(Γ , A)} {.(A +T A)} (v0 {Γ} {A}) (γ , v) = subst ∣_∣ (semWK-ty A A γ v) v
π {.(Γ , B)} {.(A +T B)} (vS {Γ} {A} {B} x) (γ , v) = subst ∣_∣ (semWK-ty A B γ v) (π x γ)


lemTy : ∀ {Γ Δ}(A : Ty Δ)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C) → ⟦ A ⟧T (⟦ δ ⟧cm γ) ≡ ⟦ A [ δ ]T ⟧T γ

lemTm : ∀ {Γ Δ}(A : Ty Δ)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C) (a : Tm A) → subst ∣_∣ (lemTy A δ γ) (⟦ a ⟧tm (⟦ δ ⟧cm γ)) ≡  ⟦ a [ δ ]tm ⟧tm γ


lemTy {Γ} {Δ} * δ γ = refl
lemTy {Γ} {Δ} (_=h_ {A} a b) δ γ = EqHom (lemTy A _ _) (lemTm _ _ _ a) (lemTm _ _ _ b) -- cong ♭ (≅-to-≡ (Eqhomo (lemTy {A = A} δ γ) (lemTm _ _ a) (lemTm _ _ b)))

⟦_⟧tm (var x) γ = π x γ
⟦_⟧tm {Γ} (JJ {Δ = Δ} x δ A) γ = subst ∣_∣ (lemTy A δ γ) (Coh Δ x A (⟦ δ ⟧cm γ))

ct-l1 : {Γ : Con}(A B : Ty Γ)(γ : ⟦ Γ ⟧C)(prf : A ≡ B) → ⟦ A ⟧T γ ≡ ⟦ B ⟧T γ
ct-l1 .B B γ refl = refl

cong⟦⟧tm : {Γ : Con}(A B : Ty Γ)(γ : ⟦ Γ ⟧C)(t : Tm A)(prf : A ≡ B) →  ⟦ t ⟦ sym prf ⟫ ⟧tm γ ≡ subst (λ x →  ∣ ⟦ x ⟧T γ ∣) prf (⟦ t ⟧tm γ)
cong⟦⟧tm .B B γ t refl = refl

⟦ • ⟧cm γ = tt
⟦ _,_ f {A} a ⟧cm γ = (⟦ f ⟧cm γ) , subst (λ x → ∣ x ∣) (sym (lemTy A f γ)) (⟦ a ⟧tm γ)

Eq-product : {A : Set}{B : A → Set}{x y : A}{m : B x}{n : B y} → (p : x ≡ y) → subst B p m ≡ n → _≡_ {_} {Σ A B} (x , m) (y , n)
Eq-product refl q = cong (λ x → _ , x) q


postulate semWK-cm' : ∀ {Γ Δ : Con}(B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
             (δ : Γ ⇒ Δ) → ⟦ δ ⟧cm γ ≡ ⟦ δ +S B ⟧cm (γ , v)

semWK-cm = semWK-cm'
{-
semWK-cm B γ v • = refl
semWK-cm B γ v (δ , a) = Eq-product (semWK-cm B γ v δ) {!!}
-}
postulate semWK-tm' : ∀ {Γ : Con}(A B : Ty Γ)(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
             (a : Tm A) → subst ∣_∣ (semWK-ty A B γ v) (⟦ a ⟧tm γ) ≡ ⟦ a +tm B ⟧tm (γ , v)


semWK-tm = semWK-tm'
{-
semWK-tm A B γ v (var x) = refl
semWK-tm .(A [ δ ]T) B γ v (JJ {Γ} {Δ} x δ A) = {!!} trans (subst-p2 (Coh' Δ x A (⟦ δ ⟧cm γ)) (semWK-ty (A [ δ ]T) B γ v)
                                                         (lemTy A δ γ)) (sym (trans (cong⟦⟧tm _ _ (γ , v) (JJ x (δ +S B) A) [+S]T) 
         (trans (cong (λ y → subst (λ x₁ → ∣ ⟦ x₁ ⟧T (γ , v) ∣) [+S]T  (subst ∣_∣ (lemTy A (δ +S B) (γ , v)) y))  prf) {!!})))
  where
    prf : (Coh' Δ x A (⟦ δ +S B ⟧cm (γ , v))) ≡ subst (λ y → ∣ ⟦ A ⟧T y ∣) (semWK-cm B γ v δ) (Coh' Δ x A (⟦ δ ⟧cm γ))
    prf = {!!}
-}


{-
ht.trans (ht.≡-subst-removable ∣_∣ (lemTy {A = B} δ γ) ((J Δ x B (⟦ δ ⟧cm γ)))) 
    (ht.sym (ht.trans (swtm-l (JJ x (δ +S A) B) (sym [+S]T) (γ , a)) (ht.trans
                                                                        (ht.≡-subst-removable ∣_∣ (lemTy (δ +S A) (γ , a))
                                                                         (J Δ x B (⟦ δ +S A ⟧cm (γ , a))))
                                                                        (ht.trans (ht.≡-to-≅ (cong (J Δ x B) (semWK-cm A γ a δ))) hrefl)) ))

-}

-- (cong≅-≋ (⟦ (A₁ [ δ ]T) +T A ⟧T (γ , a)) (λ ty t → ⟦ {!y!} ⟧tm (γ , a)) {!!}
-- {! ⟦ JJ x (δ +S A) A₁ ⟦ [+S]T A₁ δ A ⟫ ⟧tm (γ , a) !}

postulate lemTm' : ∀ {Γ Δ}(A : Ty Δ)(δ : Γ ⇒ Δ)(γ : ⟦ Γ ⟧C) (a : Tm A) → subst ∣_∣ (lemTy A δ γ) (⟦ a ⟧tm (⟦ δ ⟧cm γ)) ≡  ⟦ a [ δ ]tm ⟧tm γ
lemTm = lemTm'

-- subst

{-

lemTm .(A +T A) (δ , a) γ (var (v0 {Γ₁} {A})) = {!!}
lemTm .(A +T B) δ γ (var (vS {Γ₁} {A} {B} x)) = {!!}
lemTm .(A [ θ ]T) δ γ (JJ x θ A) = {!!}
-}
-- ⟦ JJ {Δ = Δ} x δ A ⟧tm γ ≡ Coh Δ x A (⟦ δ ⟧ γ)

{-
Id-tm : {Γ : Con}{A : Ty Γ}(t : Tm A)(γ : ⟦ Γ ⟧C) → ∣ ⟦ Tm-refl _ _ t ⟧tm γ ∣
Id-tm t γ = {!γ!}

R : (θ : Con)(isC : isContr θ) → ⟦ ε , * ⟧C → ⟦ θ ⟧C
R .(ε , *) c* t = t
R .(Γ , A , (var (vS x) =h var v0)) (ext {Γ} isC {A} x) (tt , g) = (R Γ isC (tt , g) , ⟦ var x ⟧tm (R Γ isC (tt , g))) , {!!} -- ⟦ Tm-refl _ _ (var x) ⟧tm {!!} -- {!!} , {!!}
-}

\end{code}
}