\begin{code}

module Data.Real.Operators where

open import Data.Nat using (ℕ; _⊔_) renaming (_>_ to _ℕ>_)
open import Data.Rational.Definition as ℚ₀ using (ℚ₀; ∣_∣) renaming (_+_ to _ℚ₀+_; _<_ to _ℚ₀<_; _-_ to _ℚ₀-_)
open import Data.Real.Definition
open import Data.Function
open import Data.Product
open import Level using (zero)
open import Relation.Binary.Core
open import Algebra.FunctionProperties.Core

getLb : ℝ → (ε : ℚ₀) → ℚ₀.is+ ε → ℕ
getLb (_ ,[ p ]) ε = proj₁ ∘ p ε


_+_   : Op₂ ℝ
(fa ,[ pa ]) + (fb ,[ pb ]) = (λ x → fa x ℚ₀+ fb x) ,[ (λ ε is+ → getLb (fa ,[ pa ]) ε is+ ⊔ getLb (fb ,[ pb ]) ε is+ , (λ m n m>lb n>lb → {!!})) ]
\end{code}
