
{-# OPTIONS --universe-polymorphism #-}

open import Data.Bool
open import Data.Product
open import Data.Unit
open import Level
open import Relation.Binary
open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

module quotientHomeierBool (setoid : DecSetoid zero zero) where

open DecSetoid

S = Carrier setoid

_≋_ = DecSetoid._≟_ setoid

_~_ : S → S → Bool
a ~ b = ⌊ a ≋ b ⌋

_⇨_ : Bool → Bool → Bool
true ⇨ true  = true
true ⇨ false = false
false ⇨ _    = true

infixr 3 _⇨_
infix 2 _==_
infixr 1 _⇔_

refl~ : S → Bool
refl~ x = x ~ x

refl' : ∀ x → T (refl~ x)
refl' x with x ≋ x
... | yes t = tt
... | no t  = t (refl setoid)

sym~ : S → S → Bool
sym~ x y = x ~ y ⇨ y ~ x

sym' : ∀ x y → T (sym~ x y)
sym' x y = {!!}

trans~ : S → S → S → Bool
trans~ x y z = x ~ y ∧ y ~ z ⇨ x ~ y

trans' : ∀ x y z → T (trans~ x y z)
trans' x y z = {!!}

-- postulate ext : {a b : Level}{A : Set a}{B : Set b}{f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
-- postulate ext2 : {a b : Level}{A : Set a}{B : Set b}{f g : A → B} → f ≡ g → (∀ x → f x ≡ g x)

EqClass = S → Bool

[_] : S → EqClass
[ x ] = _~_ x

_∈_ : S → EqClass → Bool
x ∈ eqc = eqc x 

-- 

_⇔_ : Bool → Bool → Bool
a ⇔ b = (a ⇨ b) ∧ (b ⇨ a)

destruct : ∀ {a b} → T (a ∧ b) → T a × T b
destruct {true} tab = tt , tab
destruct {false} ()

construct : ∀ {a b} → T a → T b → T (a ∧ b)
construct {true} ta tb = tb
construct {false} () _

if : ∀ {a b} → T (a ⇔ b) → T (a ⇨ b)
if tab = proj₁ (destruct tab)

onlyif : ∀ {a b} → T (a ⇔ b) → T (b ⇨ a)
onlyif {a} {b} tab = proj₂ (destruct {a ⇨ b} tab)


postulate _≡_ : {l : Level}{A : Set l}(a b : A) → Bool

id : {l : Level}{A : Set l} → A → A
id x = x

_==_ : Bool → Bool → Bool
_==_ true  = id 
_==_ false = not


tbb : ∀ b → T (true ⇨ b == b)
tbb true = tt
tbb false = tt

rll : ∀ b → T (b == true) → T b
rll true tbt = tbt
rll false tbt = tbt

rewriteL : ∀ {a b} → T (b == a) → T a → T b
rewriteL {true} {b} ab ta = rll b ab
rewriteL {false} {_} _ ()

rewriteR : ∀ {a b} → T (a == b) → T a → T b
rewriteR {true} ab _ = ab
rewriteR {false} _ ()

abs : ∀ {a b} → (T a → T b) → T (a ⇨ b)
abs {true} {b} f = rewriteL (tbb b) (f tt)
abs {false} {b} f = tt

app : ∀ {a b} → T (a ⇨ b) → (T a → T b)
app {true} {b} tab _ = rewriteR (tbb b) tab
app {false} tab ()

postulate ext  : {x y : S} → T ([ x ] ≡ [ y ]) → ( ∀ z → T (z ∈ [ x ] ⇔ z ∈ [ y ]))
postulate ext2 : {x y : S} → (∀ z → T (z ∈ [ x ] ⇔ z ∈ [ y ])) → T ([ x ] ≡ [ y ])

L2C1 : ∀ x y → T ([ x ] ≡ [ y ] ⇨ x ~ y)
L2C1 x y = abs
           (λ x' → app
           (onlyif {x ~ y} {y ~ y} (ext x' y)) (refl' y))

L2C2 : ∀ x y → T (x ~ y ⇨ [ x ] ≡ [ y ])
L2C2 x y = abs (λ xy → ext2 {x} {y} (λ z → construct (abs {x ~ z} (λ xz → app (trans' y x z) (app (sym' x y) xy) xz) ) (abs {y ~ z} (λ yz → app (trans' x y z) xy yz))))

Repre = S → Bool

P : Repre → Bool
P f = {!T!}