{-#  OPTIONS --type-in-type #-}
module girard where

{- Girard's paradox with Type : Type
   even though it only needs two impredicative levels.

Impredicativity for Set₀ means that given F : Set₁ → Set₀ there
is (A : Set₁) → F A : Set₀, e.g.
This corresponds to Fω and Calculus of Constructions (= Fω + dependent types).

There is a systematic formulation of Type Theories which only have Pi-types
but can have lots of universes (called sorts): the theory of PTS = Pure Type Systems.
http://en.wikipedia.org/wiki/Pure_type_system
http://dare.ubn.kun.nl/dspace/bitstream/2066/17240/1/13256.pdf
ftp://ftp.cs.kun.nl/pub/CompMath.Found/HBKJ.ps.Z
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.56.7045&rep=rep1&type=pdf (Chapter 4).
-}

PolyId : Set
PolyId = (X : Set) → X → X

pid : PolyId
pid = λ X x → x

{- Impredicative encondings -}

Nat : Set
Nat = (X : Set) → (X -> X) → X → X

zero : Nat
zero = λ X s z → z

succ : Nat → Nat
succ n = λ X s z → s (n X s z)

plus : Nat → Nat → Nat
plus m n = λ X s z → m X s (n X s z) 

mult :  Nat → Nat → Nat
mult m n = λ X s z → m X (n X s) z

-- impossible for pow

pow :  Nat → Nat → Nat
pow m n = λ X s z → n X (λ x → m X ({!!}) z) (s z)

{- we cannot prove induction (or dependent elimination).
   we can derive primitive recursion: -}

prec : (X : Set) → X → (Nat → X → X) → Nat → X
prec X z s n = n X (s n) z
-- wrong?

{- but it doesn't satisfy the equations:

prec X z s 0 = z
prec X z s (succ m) = s m (prec X z s m)

-}

{- one level of impredicativity give you a very strong system
    (much stronger than Type Theory with universes).
   two levels of impredicativity are inconsistent! 

Impredicativity for Set₀ as above +
Impredicativity for Set₁, that is given F : Set₂ → Set₁ there
is (A : Set₂) → F A : Set₁,

is inconsistent, and this is Girard's paradox. This Type Theory is called U-.

The idea is:
  we cannot have a (X : Set₁) and an injective function 

  f : ((X → Set₁) → Set₁) → X

  Read X → Set₁ as the power set. To prove this we need impredicativity for Set₀.

  On the other hand using impredicativity at Set₁ we can construct a X : Set₁ s.t.

  X ~ (X → Set₁) → Set₁

Hurken developed a simple version of Girard's paradox.
see http://www-2.cs.cmu.edu/afs/cs.cmu.edu/user/kw/www/scans/hurkens95tlca.pdf
there is also a version for Coq and Agda
but maybe rather try to understand it and do it yourself.

-}

* = Set
□ = Set
△ = Set

-- Power set

℘ : □ -> □
℘ S = S -> □

℘℘ : □ → □
℘℘ S = ℘ (℘ S)

⊥ : *
⊥ = ∀ (p : *) → p

¬_ : * -> *
¬ φ = φ -> ⊥

-- universe

U : *
U = ∀ (X : □) → (((℘℘ X) → X) → (℘℘ X))

τ : ℘℘ U -> U
τ t = \X f p -> t \x -> p (f (x X f))

σ : U -> ℘℘ U
σ s = s U \t -> τ t

Δ : ℘ U
Δ = \y -> ¬ (∀ (p : ℘ U) -> σ y p -> p (τ (σ y)))

Ω : U
Ω = τ \p -> ∀ (x : U) -> σ x p -> p x

D : Set
D = ∀ (p : ℘ U) -> σ Ω p -> p (τ (σ Ω))

lem₀ : ∀ (p : ℘ U) -> (∀ (x : U) -> σ x p -> p x) -> p Ω
lem₀ p H1 = H1 Ω \x -> H1 (τ (σ x))

lem₂ : ¬ D
lem₂ = lem₀ Δ \x H2 H3 -> H3 Δ H2 \p -> H3 \y -> p (τ (σ y))

lem₃ : D
lem₃ p = lem₀ \y -> p (τ (σ y))

loop : ⊥
loop = lem₂ lem₃