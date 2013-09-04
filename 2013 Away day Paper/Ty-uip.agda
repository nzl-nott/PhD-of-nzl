module Ty-uip where


open import Relation.Binary.PropositionalEquality
open import AIOOG
import Hedberg-Theorem
open import Equality
open import Prelude hiding (_×_)


J : {A : Set} (P : {x y : A} → x ≡ y → Set) →
    (∀ x → P {x} refl) →
    ∀ {x y} (x≡y : x ≡ y) → P x≡y
J P prefl refl = prefl _

Tydec-aux1 : {Γ : Con}{A A' : Ty Γ}{a b : Tm A}{a' b' : Tm A'} → (a =h b) ≡ (a' =h b')
      → A ≡ A'
Tydec-aux1 refl = refl

Vardec : {Γ : Con}(A : Ty Γ)(a b : Var A) → a ≡ b ⊎ (a ≡ b → ⊥)
Vardec .(A +T A) (v0 {Γ} {A}) b = {!A!}
Vardec .(A +T B) (vS {Γ} {A} {B} a) b = {!!}

Tmdec-aux1 : {Γ : Con}{A : Ty Γ}{a b : Var A} → var a ≡ var b
      → a ≡ b
Tmdec-aux1 refl = refl

Tmdec : {Γ : Con}(A : Ty Γ)(a b : Tm A) → a ≡ b ⊎ (a ≡ b → ⊥)
Tmdec A (var x) (var x₁) with Vardec A x x₁
Tmdec A (var .x₁) (var x₁) | inj₁ refl = inj₁ refl
Tmdec A (var x) (var x₁) | inj₂ y = inj₂ (λ x₂ → y (Tmdec-aux1 x₂))
Tmdec .(A [ δ ]T) (var x₁) (JJ x δ A) = inj₂ (λ())
Tmdec .(A [ δ ]T) (JJ x δ A) b = {!b!}

Tydec : {Γ : Con}(A B : Ty Γ) → A ≡ B ⊎ (A ≡ B → ⊥)
Tydec * * = inj₁ refl
Tydec * (a =h b) = inj₂ (λ())
Tydec (a =h b) * = inj₂ (λ ())
Tydec (_=h_ {A} a b) (_=h_ {B} a₁ b₁) with Tydec A B
Tydec (a =h b) (a₁ =h b₁) | inj₁ refl = {!!}
Tydec (a =h b) (a₁ =h b₁) | inj₂ y = inj₂ (λ x → y (Tydec-aux1 x))

Tyuip : (Γ : Con)(A B : Ty Γ)(p q : A ≡ B) → p ≡ q
Tyuip Γ A B = Hedberg-Theorem.decidable⇒UIP (λ {a} {p} → record { elim = J; elim-refl = λ P r → refl }) Tydec
hom' : {Γ : Con}{A A' : Ty Γ}(P : (X : Ty Γ) → (Tm X) → Ty Γ)
                {b : Tm A}{b' : Tm A'}(r : b ≅ b')
                → P A b ≡ P A' b'
hom' P {.b'} {b'} (refl .b') = refl 



ppp : {Γ : Con}{A A' : Ty Γ}{a : Tm A}{a' : Tm A'} → (r : a ≅ a')
      → A ≡ A'
ppp {Γ} {.A'} {A'} {.a'} {a'} (refl .a') = refl

{-
hom≡ : {Γ : Con}{A A' : Ty Γ}
                {a : Tm A}{a' : Tm A'}(q : a ≅ a')
                {b : Tm A}{b' : Tm A'}(r : subst Tm (ppp q) b ≡ b')
                → (a =h b) ≡ (a' =h b')
hom≡ {Γ} {.A'} {A'} {.a'} {a'} (refl .a') refl = refl

hom≡aux : {Γ : Con}{A A' : Ty Γ}(q : A ≡ A')
                {b : Tm A}{b' : Tm A'} → b ≅ b'
                → subst Tm q b ≡ b'
hom≡aux refl r = {!r!}
-}