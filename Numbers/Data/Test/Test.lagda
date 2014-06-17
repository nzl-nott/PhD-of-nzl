
\begin{code}

module Data.Test.Test where

open import Data.Integer.Setoid
open import Data.Integer.Setoid.BasicProp
open import Data.Integer.Setoid.CommutativeRing
open RingSolver using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)
open import Relation.Binary.PropositionalEquality

test : ∀ (a b c d : ℤ₀) → (a + b) * (c + d) ∼ a * c + a * d + b * c + b * d
test = solve 4 (λ a b c d → (a :+ b) :* (c :+ d) := a :* c :+ a :* d :+ b :* c :+ b :* d) zrefl


\end{code}