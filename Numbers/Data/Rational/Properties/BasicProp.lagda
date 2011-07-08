\begin{code}
module Data.Rational.Properties.BasicProp where

open import Function
open import Data.Nat using (suc) renaming (_+_ to _ℕ+_ ; _*_ to _ℕ*_)
open import Data.Integer.Setoid.Properties as ℤ₀ using () renaming (_>≤<_ to _ℤ₀>≤<_) 
open import Data.Integer' using (+_ ; -suc_; [_]; ⌜_⌝; +suc) renaming (_+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _≤_ to _ℤ≤_)
open import Data.Integer.Properties' as ℤ using (_⋆*_; _*⋆_) renaming (_≟_ to _ℤ≟_; _≤?_ to _ℤ≤?_ )
open import Data.Rational'
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core

open import Symbols

infixl 40 _>≤<_


ℤl-≤resp : ∀ {n x y} → x ≡ y → n ℤ≤ x → n ℤ≤ y
ℤl-≤resp refl = id

ℤr-≤resp : ∀ {n x y} → x ≡ y → x ℤ≤ n → y ℤ≤ n
ℤr-≤resp refl = id

\end{code}

1. Some trivial properties

a) all zero are equal

0 / m = [(0 / 1)]₌ are all 0

\begin{code}

_0~_ : ∀ {p q} → (is0 p) → (is0 q) → p ∼ q
_0~_ {.(+ 0) /suc _} {.(+ 0) /suc _} refl refl = refl

p~0 : ∀ {p} → is0 p → p ∼ qzero
p~0 {.(+ 0) /suc _} refl = refl

\end{code}

a) reflexivity: ∀ a → a ∼ a

\begin{code}

qrefl : Reflexive _∼_
qrefl {n /suc d} = refl

\end{code}

b) symmetry: ∀ a b → a ∼ b → b ∼ a

\begin{code}

qsym : Symmetric _∼_
qsym {a /suc ad} {b /suc bd} = sym

\end{code}

2. transitivity of (ℚ₀, ∼)

c) The transitivity

a = b → b = c → a = c

\begin{code}

qtrans : Transitive _∼_
qtrans {a /suc ad} {b /suc bd} {c /suc cd} a=b b=c with ℤ.0? b
qtrans {a /suc ad} {.(+ 0) /suc bd} {c /suc cd} a=b b=c | yes refl = 
  ℤ.solve0' (+ suc bd) {a} (λ ()) a=b 0~
  ℤ.solve0' (+ suc bd) {c} (λ ()) ⟨ b=c ⟩
qtrans {a /suc ad} {b /suc bd} {c /suc cd} a=b b=c | no ¬p =
  ℤ.l-integrity (b ℤ* (+ suc bd)) (ℤ.nz* b (+ suc bd) ¬p (λ ())) $ 
  ℤ.*-exchange₁ b (+ suc bd) a (+ suc cd) >≡< 
  (ℤ.*-cong b=c a=b) >≡<
  ℤ.*-exchange₂ c (+ suc bd) b (+ suc ad)

\end{code}

3. ∼ is equivalence relation for ℚ₀
reflexivity, symmetry, transitivity

\begin{code}

isEquivalenceℚ₀ : IsEquivalence _∼_
isEquivalenceℚ₀ = record 
  { refl = qrefl
  ; sym  = qsym 
  ; trans = qtrans
  }

\end{code}

The 'trans' is not only difficult to prove but also requires gives it definitely what implicit argument is. I stuck here for long time to think of write it in this way.


4. Equivalence relation is decidable

\begin{code}

_≟_   : Decidable _∼_
(a /suc ad) ≟ (b /suc bd) = (a ℤ*ℕ suc bd) ℤ≟ (b ℤ*ℕ suc ad)

\end{code}

5. (ℚ₀, ∼) is a setoid

\begin{code}

ℚ₀setoid : Setoid _ _
ℚ₀setoid = record {
    Carrier   = ℚ₀
  ;  _≈_      = _∼_
  ; isEquivalence = isEquivalenceℚ₀
  }

\end{code}

6. integrity for (ℚ₀, ∼)
a ≠ 0 → a * m = a * n → m = n

\begin{code}

integrity : ∀ a m n → (¬0 a) →  a * m ∼ a * n → m ∼ n
integrity (a /suc ad) (m /suc md) (n /suc nd) nz eqt =
  ℤ.l-integrity (a ℤ* + suc ad) (ℤ.nz* a (+ suc ad) nz (λ ())) $
  ℤ.*-exchange₃ a (+ suc ad) m (+ suc nd) >≡< 
  ℤ._*⋆_ (a ℤ* m) (ℤ.*+-simp (suc ad) (suc nd)) >≡< eqt >≡<
  ℤ._*⋆_ (a ℤ* n) ⟨ ℤ.*+-simp (suc ad) (suc md) ⟩ >≡<
  ⟨ ℤ.*-exchange₃ a (+ suc ad) n (+ suc md) ⟩

\end{code}

The integrity or cancellation rule is also a challenge. The proof here is using the integrity for ℤ,
however there is another way to prove it: multiply the inverse of 'a' to cancel it on both sides.
The problem is it requires the '*-assoc', '*-leftInverse' and '1*q=q' which will been proven in latter part.

7. (ℚ₀, ∼, ≤) is a decidable total order

a) ≤ is decidable

\begin{code}

_≤?_ : Decidable _≤_
(a /suc ad) ≤? (b /suc bd) = (a ℤ*ℕ suc bd) ℤ≤? (b ℤ*ℕ suc ad)

\end{code}

b) reflexivity: a ∼ b → a ≤ b

\begin{code}

refl′ : _∼_ ⇒ _≤_
refl′ {_ /suc _} {_ /suc _} m∼n = ℤ.refl′ m∼n

\end{code}

b) transitivity: a ≤ b → b ≤ c → a ≤ c

\begin{code}

trans′ : Transitive _≤_
trans′ {a /suc ad} {b /suc bd} {c /suc cd} a≤b b≤c =
  ℤ.integrity′ {a ℤ* + suc cd} {c ℤ* + suc ad} bd $
  ℤr-≤resp {+ suc bd ℤ* (c ℤ* + suc ad)} (ℤ.*-ex₁ (+ suc cd) a (+ suc bd)) $
  ℤl-≤resp {+ suc cd ℤ* (a ℤ* + suc bd)} (ℤ.*-ex₁ (+ suc ad) c (+ suc bd)) $
  (ℤ.*-cong′ {a ℤ* + suc bd} {b ℤ* + suc ad} (suc cd) a≤b) ℤ₀>≤<
  (ℤ.refl′ (ℤ.*-ex₁ (+ suc cd) b (+ suc ad))) ℤ₀>≤<
  ℤ.*-cong′ {b ℤ* + suc cd} {c ℤ* + suc bd} (suc ad) b≤c

_>≤<_ : Transitive _≤_
_>≤<_ {a} = trans′ {a}

\end{code}

c) ≤ respect ∼

\begin{code}

≤resp : _≤_ Respects₂ _∼_
≤resp = (λ {a} b∼c a≤b → trans′ {a} a≤b $ refl′ b∼c) ,
         λ {_} {_} {c} b∼c b≤a → trans′ {c} (refl′ (qsym b∼c)) b≤a


\end{code}

d) (ℚ₀, ∼, ≤) is preorder

\begin{code}


≤isPreorder : IsPreorder _∼_ _≤_
≤isPreorder =  record
  { isEquivalence = isEquivalenceℚ₀
  ; reflexive     = refl′
  ; trans         = λ {a} → trans′ {a}
--   ; ∼-resp-≈      = ≤resp
  }


\end{code}

e) antisymmetric
a ≤ b → b ≤ a → a ∼ b

\begin{code}

antisym : Antisymmetric _∼_ _≤_
antisym {a /suc ad} {b /suc bd} = ℤ.antisym


\end{code}

f) total
a ≤ b or b ≤ a

\begin{code}

total : Total _≤_
total (a /suc ad) (b /suc bd) = ℤ.total (a ℤ* + suc bd) (b ℤ* + suc ad)

\end{code}

g) (ℚ₀, ∼, ≤) is a decidable total order

\begin{code}

decTotalOrder : DecTotalOrder _ _ _
decTotalOrder = record
  { Carrier         = ℚ₀
  ; _≈_             = _∼_
  ; _≤_             = _≤_
  ; isDecTotalOrder = record
      { isTotalOrder = record
          { isPartialOrder = record
              { isPreorder = ≤isPreorder
              ; antisym  = λ {a} {b} → antisym {a} {b}
              }
          ; total = total
          }
      ; _≟_  = _≟_
      ; _≤?_ = _≤?_
      }
  }

\end{code}

The amount of time taken to prove the transitivity of ≤ for ℚ₀ is also comparatively more than the other small properties of the decidable total order. The same problem occurs here again that it requires to gives all the implicit arguments (Maybe due to use projection instead of pattern match when defining the operators).


f) same denominator

\begin{code}

combine : ∀ a b ad bd → ad ≡ bd → (a /suc ad) + (b /suc bd) ∼ (a ℤ+ b) /suc ad
combine a b ad .ad refl = ⟨ ℤ.distʳ (+suc ad) a b ⟩ ⋆* +suc ad >≡< 
  (ℤ.*-assoc (a ℤ+ b) (+suc ad) (+suc ad) >≡<
  (a ℤ+ b) *⋆ (ℤ.*+-simp (suc ad) (suc ad)))

\end{code}
