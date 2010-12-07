{-#  OPTIONS --type-in-type #-}
module nuo3a where

-- http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.39.1953&rep=rep1&type=pdf

open import Data.Empty
open import Data.Unit
open import Data.Bool

data set : Set where
  idx : (I : Set) → (I → set) → set

infix 4 _∈_

data _∈_ : set → set → Set where
  inn : (I : Set)(f : I → set)(i : I) → f i ∈ idx I f

_∉_ : set → set → Set
a ∉ b = (a ∈ b) → ⊥
 
[] : set
[] = idx ⊥ (λ ())

[[]] : set
[[]] = idx ⊤ (λ _ → [])

[[[]],[]] : set
[[[]],[]] = idx Bool (λ b → if b then [] else [[]])

{- Encode classical set theory in type theory using this idea.
   Due to Peter Aczel. http://www.springerlink.com/content/jkt3tlf6kdh8la8b/fulltext.pdf
-}

data GoodSet : Set where good : (s : set) → (s ∈ s → ⊥) → GoodSet

pr : GoodSet → set
pr (good s _) = s

Russell : set
Russell = idx GoodSet pr

R∈R = Russell ∈ Russell

R∉R = R∈R → ⊥

-- if some set is in Russell, then it is not the subset of itself

lem1 : ∀ {s} → s ∈ Russell → s ∉ s
lem1 (inn .GoodSet .pr (good _ y)) = y

lem1-1 : R∈R → R∉R
lem1-1 = lem1

-- if some set is not the subset of itself, it is in Russell

lem2 : ∀ {s} → s ∉ s → s ∈ Russell
lem2 {s} y = inn GoodSet pr (good s y)

lem2-1 : R∉R → R∈R
lem2-1 = lem2


-- Russell is not in itself

lem3 : R∉R
lem3 r∈r = lem1 r∈r r∈r

lem4 : R∈R
lem4 = lem2 lem3

{-
http://www.amazon.co.uk/Logicomix-Search-Truth-Apostolos-Doxiadis/dp/0747597200/ref=sr_1_1?ie=UTF8&qid=1288259778&sr=8-1
-}
pcf : ⊥
pcf = lem3 lem4

