module Eq where

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Bool

{- assume we don't have equality. -}

Eqℕ : ℕ → ℕ → Set
Eqℕ zero zero = ⊤
Eqℕ zero (suc n) = ⊥
Eqℕ (suc n) zero = ⊥
Eqℕ (suc n) (suc m) = Eqℕ n m

reflℕ : (n : ℕ) → Eqℕ n n
reflℕ zero = _
reflℕ (suc n) = reflℕ n

substℕ : (m n : ℕ) → Eqℕ m n → (P : ℕ → Set) → P m → P n
substℕ zero zero p P x = x
substℕ zero (suc n) () P x
substℕ (suc m) zero () P x
substℕ (suc m) (suc n) p P x = substℕ m n p (λ i → P (suc i)) x

{- prove J for this type -}

Eqℕ→ℕ : (ℕ → ℕ) → (ℕ → ℕ) → Set
Eqℕ→ℕ f g = (n : ℕ) → Eqℕ (f n) (g n)

reflℕ→ℕ : (f : ℕ → ℕ) → Eqℕ→ℕ f f
reflℕ→ℕ f = λ n → reflℕ (f n)

substℕ→ℕ : (f g : ℕ → ℕ) → Eqℕ→ℕ f g → (P : (ℕ → ℕ) → Set) → P f → P g
substℕ→ℕ f g p P x = {!!} -- unprovable

{- exercise: Define EqBool and EqBool→Bool -}

EqBool : Bool → Bool → Set
EqBool b c = {!!}
{- + refl, subst -}

Bool→Bool : Set
Bool→Bool = {!!}

app : Bool→Bool → Bool → Bool
app f x = {!!}

abs : (Bool → Bool) → Bool→Bool
abs f = {!!}

βBool : (f : Bool → Bool)(x : Bool) → EqBool (app (abs f) x) (f x)
βBool f x = {!!}

EqBool→Bool : (Bool→Bool) → (Bool→Bool) → Set
EqBool→Bool f g = (n : Bool) → EqBool (app f n) (app g n)

{- define refl and subst -}

{- But does the same work for Nat? -}
