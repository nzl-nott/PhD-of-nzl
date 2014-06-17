module Eq where

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Product

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
EqBool true true = ⊤
EqBool true false = ⊥
EqBool false true = ⊥
EqBool false false = ⊤
{- + refl, subst -}

reflB : (b : Bool) → EqBool b b
reflB true = tt
reflB false = tt

substB : (b c : Bool) → EqBool b c → (P : Bool → Set) → P b → P c
substB true true p P x = x
substB true false () P x
substB false true () P x
substB false false p P x = x

Bool→Bool : Set
Bool→Bool = Bool × Bool

app : Bool→Bool → Bool → Bool
app (t , f) true = t
app (t , f) false = f

abs : (Bool → Bool) → Bool→Bool
abs f = f true , f false

βBool : (f : Bool → Bool)(x : Bool) → EqBool (app (abs f) x) (f x)
βBool f true = reflB (f true)
βBool f false = reflB (f false)

EqBool→Bool : (Bool→Bool) → (Bool→Bool) → Set
EqBool→Bool f g = (n : Bool) → EqBool (app f n) (app g n)

{- define refl and subst -}

reflBool→Bool : (f : Bool→Bool) → EqBool→Bool f f
reflBool→Bool f = λ b → reflB (app f b)

EqBool→Bool' : (Bool→Bool) → (Bool→Bool) → Set
EqBool→Bool' (ft , ff) (gt , gf) = EqBool ft gt × EqBool ff gf

BB' : (b c : Bool→Bool) → EqBool→Bool b c → EqBool→Bool' b c
BB' b c p = p true , p false

substBool→Bool :  (b c : Bool→Bool) → EqBool→Bool b c → (P : Bool→Bool → Set) → P b → P c
substBool→Bool b c p P x with BB' b c p
substBool→Bool (true , true) (true , true) p P x | t , f = x
substBool→Bool (true , true) (true , false) p P x | t , ()
substBool→Bool (true , false) (true , true) p P x | t , ()
substBool→Bool (true , false) (true , false) p P x | t , f = x
substBool→Bool (true , y) (false , y') p P x | () , f
substBool→Bool (false , y) (true , y') p P x | () , f
substBool→Bool (false , true) (false , true) p P x | t , f = x
substBool→Bool (false , true) (false , false) p P x | t , ()
substBool→Bool (false , false) (false , true) p P x | t , ()
substBool→Bool (false , false) (false , false) p P x | t , f = x

{- But does the same work for Nat? -}
