--------------------------------------------------
The advanced properties for ℤ₀

\begin{code}

module Data.Integer.Properties.AdvancedProp where

open import Algebra
open import Data.Function
open import Data.Nat using ()
  renaming (suc to nsuc; _+_ to  _ℕ+_;  _*_ to  _ℕ*_)
open import Data.Integer.Definition
open import Data.Integer.Properties.BasicProp
open import Data.Integer.Properties.CommutativeRing
import Data.Integer.Setoid.Properties as ℤ₀
open import Data.Nat.Properties+ as ℕ using (_+=_; _+⋆_)
open import Relation.Binary.PropositionalEquality
open import Symbols

infixr 42  _*⋆_
infixr 42  _⋆*_

\end{code}

if m * n ∼ 0 and m is not 0 then n must be 0

\begin{code}

solve0 : ∀ m {n} → (p : ¬0 m) → m * n ≡ + 0 → n ≡ + 0
solve0 m p eqt = ⌞ ℤ₀.solve0 ⌜ m ⌝ (⌜nz⌝ p) (complete eqt) ⌟

solve0' : ∀ m {n} → (p : ¬0 m) → n * m ≡ + 0 → n ≡ + 0
solve0' m {n} p eqt = solve0 m p (*-comm m n >≡< eqt)

\end{code}

integrity of ℤ
(left & right cancellation)

\begin{code}

l-integrity : ∀ {m n} a → (p : ¬0 a) → a * m ≡ a * n → m ≡ n
l-integrity a p eqt = ⌞ ℤ₀.integrity ⌜ a ⌝ (⌜nz⌝ p) (complete eqt)  ⌟

r-integrity : ∀ {m n} a → (p : ¬0 a) → m * a ≡ n * a → m ≡ n
r-integrity {m} {n} a p eqt = l-integrity a p $
  *-comm a m >≡< eqt >≡< *-comm n a

\end{code}

* congruence

\begin{code}

_*⋆_ : ∀ {p q} m → p ≡ q → m * p ≡ m * q
_*⋆_ _ refl = refl

_⋆*_ : ∀ {p q} → p ≡ q → (m : ℤ) → p * m ≡ q * m
_⋆*_ refl _ = refl

\end{code}

* exchange functions

\begin{code}

*-ex₁ : ∀ a b c → a * (b * c) ≡ c * (b * a)
*-ex₁ a b c = a *⋆ *-comm b c >≡< *-comm a (c * b) >≡<
  *-assoc c b a

*-ex₂ : ∀ a b c → (a * b) * c ≡ (a * c) * b
*-ex₂ a b c = *-comm (a * b) c >≡< ⟨ *-assoc c a b ⟩ >≡<
  *-comm c a ⋆* b

*-ex₃ : ∀ a b c → (a * b) * c ≡ c * (b * a)
*-ex₃ a b c = *-comm a b ⋆* c >≡< *-comm (b * a) c

*-exchange₁ : ∀ a b c d → (a * b) * (c * d) ≡ (a * d) * (c * b)
*-exchange₁ a b c d =  *-assoc a b (c * d) >≡<
  a *⋆ (*-ex₁ b c d) >≡<
  ⟨ *-assoc a d (c * b) ⟩

*-exchange₂ : ∀ a b c d → (a * b) * (c * d) ≡ (c * b) * (a * d)
*-exchange₂ a b c d = ⟨ *-assoc (a * b) c d ⟩ >≡<
  ((*-assoc a b c) >≡< a *⋆ *-comm b c  >≡< 
  *-comm a (c * b)) ⋆* d >≡<
  *-assoc (c * b) a d

*-exchange₃ : ∀ a b c d → (a * b) * (c * d) ≡ (a * c) * (b * d)
*-exchange₃ a b c d = *-assoc a b (c * d) >≡<
  a *⋆ (⟨ *-assoc b c d ⟩ >≡< *-comm b c ⋆* d 
  >≡< *-assoc c b d) >≡<
  ⟨ *-assoc a c (b * d) ⟩

*-exchange₄ : ∀ a b c d → (a * b) * (c * d) ≡ (a * c) * (d * b)
*-exchange₄ a b c d = *-assoc a b (c * d) >≡<
  a *⋆ (*-comm b (c * d) >≡< 
  *-assoc c d b) >≡<
  ⟨ *-assoc a c (d * b) ⟩

\end{code}

if both m and n are not 0 then m * n is not 0

\begin{code}

nz*  : ∀ m n → (¬0 m) → (¬0 n) → ¬0 (m * n)
nz* m n nzm nzn = λ x → nzn (solve0 m nzm x)


\end{code}

useful functions for rational numbers

\begin{code}

*+-simp' : ∀ a b → (+suc a) * (+suc b) ≡ + ((nsuc a) ℕ* (nsuc b))
*+-simp' a b = sound $ nsuc ⋆ 
  (ℕ.n+0≡n {b ℕ+ a ℕ* nsuc b} += ⟨ ℕ.n*0+0=0 {a} ⟩)

*+-simp : ∀ a b → (+ a) * (+ b) ≡ + (a ℕ* b)
*+-simp a b = sound $ ℕ.n+0≡n {a ℕ* b} += ⟨ ℕ.n*0+0=0 {a} ⟩

-*cong : ∀ m n → m * n ≡ (- m) * (- n)
-*cong m n = ⟨ -out m (- n) >≡< -_ ⋆ (*-comm m (- n) >≡<
  -out n m) >≡< (-inv >≡< *-comm n m) ⟩

\end{code}