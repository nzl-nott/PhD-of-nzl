\begin{code}

module cohEqJ where

open import Relation.Binary.PropositionalEquality

postulate _~'_ : {A : Set} → A → A → Set

data U : Set
postulate El : U → Set

data U where
  UU : U
  _~_ : {A : U} → El A → El A → U


postulate refl~ : {A : U}{x : El A} → El (x ~ x)


postulate 
  J~ : {A : U}{a : El A}
     (P : {a' : El A} → El (a ~ a') → U)
    → El (P refl~)
    → {a' : El A}(p : El (a ~ a')) → El (P p)


data U' : Set
postulate El' : U → Set


data U' where
  UU : U'
  _~_ : {A : U} → El' A → El' A → U'

postulate isContr : U' → 

postulate coh : ∀{Γ Δ} → isContr Δ → (δ : Γ ⇒ Δ)
              → (A : U') → El' (a ~ b)

\end{code}