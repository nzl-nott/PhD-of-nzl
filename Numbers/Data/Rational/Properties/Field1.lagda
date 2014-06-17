\begin{code}
module Data.Rational.Properties.Field1 where

open import Algebra
open import Algebra.Structures
open import Data.Nat using (suc) renaming (_*_ to _ℕ*_)
open import Function
open import Data.Integer' using (+_; -suc_; [_]; ⌜_⌝; +suc)
  renaming (_+_ to _ℤ+_ ; _*_ to _ℤ*_; -_ to ℤ-_)
open import Data.Integer.Properties' as ℤ' using (_*⋆_ ; _⋆*_)
open import Data.Nat.Properties+ as ℕ using (_+⋆_)
open import Data.Rational'
open import Data.Rational.Properties.BasicProp
open import Relation.Binary.Core using (_≡_)


import Algebra.FunctionProperties as P; open P _∼_
open import Symbols

private
  module ℤ where
    open CommutativeRing ℤ'.commutativeRing public
    0+z≡z = proj₁ +-identity
    z+0≡z = proj₂ +-identity
    z*1≡z = proj₂ *-identity
    distʳ = proj₂ distrib


{-
open CommutativeRing ℤ.commutativeRing using (*-cong; +-identity; *-identity) renaming (+-comm to ℤ+-comm ; +-cong to ℤ+-cong ; *-assoc to ℤ*-assoc ; +-assoc to ℤ+-assoc ; ;*-comm to ℤ*-comm)
-}


\end{code}

(ℚ₀, ∼, +, *, 0, 1) is a Field

ℚ₀ has inverse so it is not only a commutative ring, but even a field.


1. + Identity

a) zero is left neutral (left identity) for addition
0 + q = q

\begin{code}

0+q≡q : LeftIdentity qzero _+_
0+q≡q (a /suc b) = ℤ.*-cong (ℤ.0+z≡z (a ℤ* + 1) >≡< ℤ.z*1≡z a) $
  +suc ⋆ ⟨ ℕ.n+0≡n ⟩

\end{code}

Note: 'qzero' is the representative zero of rational numbers which I defined before.

b) zero is right neutral (right identity) for addition
q + 0 = q

\begin{code}

q+0≡q : RightIdentity qzero _+_
q+0≡q (a /suc b) = ℤ.*-cong (ℤ.z+0≡z (a ℤ* + 1) >≡< ℤ.z*1≡z a) $
  +suc ⋆ ⟨ ℕ.n*1≡n b ⟩

\end{code}

As the problem of ring solver I mentioned before that it will lead to crash of Agda at least on my own computer, I have to using all the properties of ℤ to prove the properties of ℚ₀ step by step.

2. + Commutativity

a + b = b + a

\begin{code}

+-comm : Commutative _+_
+-comm (a /suc ad) (b /suc bd) = ℤ.*-cong (ℤ.+-comm (a ℤ* +suc bd) (b ℤ* +suc ad))
  $ +_ ⋆ ℕ.*-comm (suc bd) (suc ad)

\end{code}

3. + Associativity

(a + b) + c = a + (b + c)

\begin{code}

ass-lem : ∀ a b c d e f → (a ℤ* (+suc b) ℤ+ c ℤ* (+suc d)) ℤ* (+suc e) ℤ+ f ℤ* (+ ((suc d) ℕ* (suc b)))
  ≡ a ℤ* (+ ((suc b) ℕ* (suc e))) ℤ+ (c ℤ* (+suc e) ℤ+ f ℤ* (+suc b)) ℤ* (+suc d)

ass-lem a b c d e f = ℤ.+-cong (ℤ.distʳ (+suc e) (a ℤ* (+suc b)) (c ℤ* (+suc d)) >≡<
  (ℤ.+-cong (ℤ.*-assoc a (+suc b) (+suc e)) (ℤ'.*-ex₂ c (+suc d) (+suc e)))) (f *⋆ (⟨ ℤ'.*+-simp (suc d) (suc b) ⟩ >≡<
  ℤ.*-comm (+suc d) (+suc b)) >≡< ⟨ ℤ.*-assoc f (+suc b) (+suc d) ⟩) >≡<
  ℤ.+-assoc (a ℤ* (+suc b ℤ* +suc e)) (c ℤ* +suc e ℤ* +suc d) (f ℤ* +suc b ℤ* +suc d) >≡<
  ℤ.+-cong (a *⋆ ℤ'.*+-simp (suc b) (suc e)) ⟨ (ℤ.distʳ (+suc d) (c ℤ* +suc e) (f ℤ* +suc b)) ⟩

+-assoc : Associative _+_
+-assoc (a /suc ad) (b /suc bd) (c /suc cd) = ℤ.*-cong (ass-lem a bd b ad cd c) $
  +_ ⋆ ⟨ ℕ.*-assoc (suc ad) (suc bd) (suc cd) ⟩

\end{code}

4. (_+_, -_) Inverse

a) left inverse
a + (- a) = 0

\begin{code}

+-rightInverse : RightInverse qzero -_ _+_
+-rightInverse (a /suc ad) = (⟨ ℤ.distʳ (+suc ad) a (ℤ- a) ⟩ >≡< ℤ'.+-rightInverse a ⋆* +suc ad) ⋆* (+ 1)
\end{code}

b) right inverse
(- a) + a = 0

\begin{code}

+-leftInverse : LeftInverse qzero -_ _+_
+-leftInverse (a /suc ad) = (⟨ ℤ.distʳ (+suc ad) (ℤ- a) a ⟩ >≡< ℤ'.+-leftInverse a ⋆* +suc ad)
                              ⋆* (+ 1)

+-inverse : Inverse qzero -_ _+_
+-inverse = +-leftInverse , +-rightInverse

\end{code}


11. + preserves =

a) some lemmas

\begin{code}

\end{code}

b) a = b → c = d → a + c = b + d

\begin{code}

+-cong-lem : ∀ a b c d e f → (a ℤ* (+ b) ℤ+ c ℤ* (+ d)) ℤ* (+ (e ℕ* f)) ≡
  a ℤ* (+ e) ℤ* ((+ b) ℤ* (+ f)) ℤ+ c ℤ* (+ f) ℤ* ((+ e) ℤ* (+ d))
+-cong-lem a b c d e f = (a ℤ* + b ℤ+ c ℤ* + d) *⋆ ⟨ ℤ'.*+-simp e f ⟩ >≡<
  ℤ.distʳ (+ e ℤ* + f) (a ℤ* + b) (c ℤ* + d) >≡<
  ℤ.+-cong (ℤ'.*-exchange₃ a (+ b) (+ e) (+ f)) (ℤ'.*-exchange₁ c (+ d) (+ e) (+ f))

+-cong : ∀ {a b c d} → a ∼ b → c ∼ d → a + c ∼ b + d
+-cong {a /suc ad} {b /suc bd} {c /suc cd} {d /suc dd} a=b c=d = 
  +-cong-lem a (suc cd) c (suc ad) (suc bd) (suc dd) >≡<
  ℤ.+-cong (ℤ.*-cong a=b (ℤ.*-comm (+suc cd) (+suc dd)))
    (ℤ.*-cong c=d (ℤ.*-comm (+suc bd) (+suc ad))) >≡<
  ⟨ +-cong-lem b (suc dd) d (suc bd) (suc ad) (suc cd) ⟩

\end{code}

12. -_ preserves ≡

a = b → - a = - b

\begin{code}

⁻¹-cong : ∀ {a b} → a ∼ b → - a ∼ - b
⁻¹-cong {a /suc ad} {b /suc bd} a=b = ℤ'.-out a (+suc bd) >≡< ℤ-_ ⋆ a=b >≡< ⟨ ℤ'.-out b (+suc ad) ⟩

\end{code}


\begin{code}

+-isAbelianGroup : IsAbelianGroup _∼_ _+_ qzero -_
+-isAbelianGroup = record
      { isGroup = record
        { isMonoid = record
          { isSemigroup = record
            { isEquivalence = isEquivalenceℚ₀
            ; assoc         = +-assoc
            ; ∙-cong        = +-cong
            }
          ; identity = 0+q≡q , q+0≡q
          }
        ; inverse = +-inverse
        ; ⁻¹-cong = ⁻¹-cong
        }
        ; comm = +-comm
     }


\end{code}
