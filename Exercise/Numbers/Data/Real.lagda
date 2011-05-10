\begin{code}

module Data.Real where

open import Data.Empty
open import Data.Nat using (ℕ ; fold ; pred ; s≤s ; z≤n) renaming (_<_ to _ℕ<_ ; _*_ to _ℕ*_)
open import Data.Product
open import Data.Integer' using (ℤ ; +_)
open import Data.Rational' using (ℚ₀ ; _/suc_ ; _∼_ ; abscanc) renaming (_+_ to _ℚ₀+_; ∣_∣ to ℚ₀∣_∣ ; _-_ to _ℚ₀-_; _≤_ to _ℚ₀≤_ ; _<_ to _ℚ₀<_)

open import Relation.Binary.Core

\end{code}

first, we could axiomatise the real numbers

postulate ℝ : Set

postulate ∣_∣ : ℝ → ℝ

postulate _==_ _+_ _-_ _*_ _/_ : ℝ → ℝ → ℝ

postulate _≤_ _≥_ _<_ _>_ : ℝ → ℝ → Set

postulate zero one : ℝ


ℕ2ℝ : ℕ → ℝ
ℕ2ℝ ℕ.zero = zero
ℕ2ℝ (ℕ.suc n) = ℕ2ℝ n + one 


ℤ2ℝ : ℤ → ℝ
ℤ2ℝ (+ n) = ℕ2ℝ n
ℤ2ℝ (ℤ.-suc_ ℕ.zero) = zero - one
ℤ2ℝ (ℤ.-suc_ (ℕ.suc n)) = ℤ2ℝ (ℤ.-suc_ n) - one

ℚ2ℝ : ℚ₀ → ℝ
ℚ2ℝ (n /suc d) = ℤ2ℝ n / ℕ2ℝ (ℕ.suc d)


data cauℝ (r : ℝ) : Set where
  cr : (f : ℕ → ℚ₀)(p : (n : ℕ) → ∣ ℚ2ℝ (f n) - r ∣ < ℚ2ℝ (+ 1 /suc pred (2 ^ n))) → cauℝ r


the signed digit representation

data Digit : Set where
  -l o l : Digit


data SignedDigit : ℝ → Set where
  signedDigit : (r : ℝ)
                → (r )


Let R be the set of Cauchy sequences of rational numbers. That is, sequences
x1,x2,x3,... of rational numbers such that for every rational ε > 0, there exists an integer N such that for all natural numbers m,n > N, |xm-xn|<ε. Here the vertical bars denote the absolute value.

record cauℝ : Set where
  field
    f : ℕ → ℚ₀
    p : ∀ ε → is+ ε → ∃ λ lb → ((m n : ℕ) → (m ℕ> lb) → (n ℕ> lb) →  ℚ₀∣ (f m) - (f n) ∣ ℚ₀< ε )


We can choose 2^(-n) as the bound for the cauchy sequence.


\begin{code}

_^_ : ℕ → ℕ → ℕ
x ^ y = fold 1 (_ℕ*_ x) y


-- Cauchy sequences with bounded rate of convergence
-- We will use it as the representation of real numbers

record cauchy : Set where
  constructor f:_p:_
  field
    f : ℕ → ℚ₀
    p : (n m : ℕ) → (n ℕ< m) → 
        ℚ₀∣ (f m) ℚ₀- (f n) ∣ ℚ₀< ((+ 1) /suc pred (2 ^ n))

-- Can we set the + 1 to + start where start is certain positive number?

ℝ = cauchy

postulate _resp_ : ∀ {a b c} → b ℚ₀< c → a ≡ b → a ℚ₀< c

emb : ℚ₀ → ℝ
emb q = f: (λ _ → q) p: λ n m n<m → (s≤s z≤n) resp (abscanc q)


_~_ : ℝ → ℝ → Set
(f: f p: p) ~ (f: f' p: p') = (n m : ℕ) → n ℕ< m →
              ℚ₀∣ f m ℚ₀- f' m ∣ ℚ₀< (+ 1) /suc pred (2 ^ n)



abs-out : ∀ a b a' b' → ℚ₀∣ (a ℚ₀+ a') ℚ₀- (b ℚ₀+ b') ∣  ℚ₀≤ ℚ₀∣ a ℚ₀- b ∣  ℚ₀+ ℚ₀∣ a' ℚ₀- b' ∣ 
abs-out ab a' b' = {!!}


add-pre : ∀ {a b c d} → a ℚ₀< b → c ℚ₀< d → a ℚ₀+ c ℚ₀< b ℚ₀+ d
add-pre = {!!}


trans' : ∀ {a b c d} → a ℚ₀≤ d → b ℚ₀< c → a ℚ₀< c
trans' = {!!}

changeR : ∀ {a b c d} → (b ℚ₀+ c) ∼ d → a ℚ₀< b ℚ₀+ c → a ℚ₀< d
changeR = {!!}
 

_+_ : ℝ → ℝ → ℝ
(f: f p: p) + (f: f' p: p') = f: (λ x → f (2 ℕ* x) ℚ₀+ f' (2 ℕ* x)) p: λ n m x → {!!} -- trans' (abs-out (f (2 ℕ* m)) (f' (2 ℕ* m)) (f (2 ℕ* n)) (f' (2 ℕ* n))) (changeR {!!} (add-pre (p n m x) (p' n m x)))

\end{code}
