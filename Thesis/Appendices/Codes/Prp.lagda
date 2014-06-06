\begin{code}
open import Level
open import Relation.Binary.PropositionalEquality

module Prp (ext : Extensionality zero zero) where

open import Data.Product

Prp : Set₁
Prp = Σ[ A ∶ Set ] ({a b : A} → a ≡ b)

∣_∣ : Prp → Set
∣_∣ = proj₁

isP : (P : Prp) → {a b : ∣ P ∣} → a ≡ b
isP = proj₂
\end{code}

We need to postulate that the property is proof irrelevant

\begin{code}

postulate prf-irr : (A B : Prp) → ∣ A ∣ ≡ ∣ B ∣ → A ≡ B 

\end{code}

Prp is closed under Π-types
universal quantification

\begin{code}


∀' : (A : Set)(P : A → Prp) → Prp
∀' A P = ((x : A) → ∣ P x ∣) , ext (λ x → isP (P x))


syntax ∀' A (λ x → B) = ∀'[ x ∶ A ] B

infixr 2 _⇒_

_⇒_ : (A B : Prp) → Prp
A ⇒ B = ∀' ∣ A ∣ (λ _ → B)

\end{code}

Prp is closed under Σ-types
existential quantification
\begin{code}

exist-lem : (P : Prp)(Q : ∣ P ∣ → Prp)(a b : Σ ∣ P ∣ (λ x → ∣ Q x ∣)) → a ≡ b
exist-lem P Q (ap , aq) (bp , bq) with isP P {ap} {bp}
exist-lem P Q (ap , aq) (.ap , bq) | refl with isP (Q ap) {aq} {bq}
exist-lem P Q (ap , aq) (.ap , .aq) | refl | refl = refl

∃' : (P : Prp)(Q : ∣ P ∣ → Prp) → Prp
∃' P Q = (Σ ∣ P ∣  (λ x →  ∣ Q x ∣)) , λ {a} {b} → exist-lem P Q a b


syntax ∃' A (λ x → B) = ∃'[ x ∶ A ] B

infixr 3 _∧_

_∧_ : (A B : Prp) → Prp
A ∧ B = ∃' A (λ _ → B)

\end{code}
