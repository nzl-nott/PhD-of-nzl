\begin{code}


open import Level
open import Relation.Binary.PropositionalEquality as PE hiding (refl ; sym ; trans; isEquivalence; [_])


module ImpreQuotient  (ext : ∀{i j} → Extensionality i j) where

open import Data.Product hiding (∃)
open import Level
open import Relation.Binary.PropositionalEquality

_⇔_ : {i j : Level} (A : Set i) (B : Set j) → Set _
A ⇔ B = (A → B) × (B → A)

ishProp : ∀{i} → (A : Set i) → Set i
ishProp A = ∀(a b : A) → a ≡ b

hProp = Σ Set ishProp

Σhp : (A : hProp)(B : proj₁ A → hProp) → hProp
Σhp (A , p) B = (Σ A (λ x → proj₁ (B x))) , (λ a b → {!p!})

hProp₁ = Σ Set₁ ishProp

postulate RR1 : hProp₁ → hProp

postulate RR1-rule : ∀ (x : hProp₁) → (proj₁ (RR1 x)) ⇔ proj₁ x

ishSet : ∀{i} → (A : Set i) → Set i
ishSet A = ∀(a b : A) → ishProp (a ≡ b)

hSet = Σ Set ishSet

hSet₁ = Σ Set₁ ishSet


_≅_ : ∀ {i j}(A : Set i)(B : Set j) → Set _
A ≅ B = Σ (A → B) (λ f → Σ (B → A) (λ g → (∀ x → g (f x) ≡ x) × (∀ x → f (g x) ≡ x)) )

postulate RR2 : hSet₁ → hSet

postulate RR2-rule : ∀ (x : hSet₁) → (proj₁ (RR2 x)) ≅ proj₁ x

∥_∥ : Set → hProp
∥ X ∥ = RR1 (((P : hProp) → (X → proj₁ P) → proj₁ P) , (λ a b → ext (λ P → ext (λ x₁ → proj₂ P _ _))))

∃ : (A : Set)(P : A → hProp) → hProp
∃ A P =  ∥ Σ A (λ a → proj₁ (P a)) ∥

EqClass : (A : Set)(P : A → hProp) → hProp
EqClass A P = ∃ A P ∧ ?

{-
_/_ : (A : Set)(_∼_ : A → A → hProp) → hSet
A / _∼_ = RR2 ((Σ (A → hProp) (λ P → Σhp {!∃ A P!}  {!!})) , {!!}) -- Σ (A → hProp) ? -- (λ P → EqClass A P)
-}



\end{code}