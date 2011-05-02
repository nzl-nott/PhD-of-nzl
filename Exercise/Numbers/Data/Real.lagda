\begin{code}

module Data.Real where

open import Data.Nat using (ℕ ; fold ; pred) renaming (_<_ to _ℕ<_ ; _*_ to _ℕ*_)
open import Data.Product
open import Data.Integer' using (ℤ ; +_)
open import Data.Rational' using (ℚ₀ ; _/suc_) renaming (∣_∣ to ℚ₀∣_∣ ; _-_ to _ℚ₀-_; _<_ to _ℚ₀<_)



\end{code}

first, we could axiomatise the real numbers


\begin{code}

postulate ℝ : Set

postulate ∣_∣ : ℝ → ℝ

postulate _==_ _+_ _-_ _*_ _/_ : ℝ → ℝ → ℝ

postulate _≤_ _≥_ _<_ _>_ : ℝ → ℝ → Set

postulate zero one : ℝ

\end{code}


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
  field
    f : ℕ → ℚ₀
    p : (n : ℕ) → ∀ (m : ℕ) → (n ℕ< m) → ℚ₀∣ (f m) ℚ₀- (f n) ∣ ℚ₀< ((+ 1) /suc pred (2 ^ n))


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

\end{code}

the signed digit representation

\begin{code}

data Digit : Set where
  -l o l : Digit


data SignedDigit : ℝ → Set where
  signedDigit : (r : ℝ)
                → (r )

\end{code}