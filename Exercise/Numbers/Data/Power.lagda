
\begin{code}

module Data.Power where

open import Data.Nat as ℕ using (ℕ ; suc)
  renaming ( _+_ to _ℕ+_ ;  _∸_ to _ℕ-_ ; _*_ to _ℕ*_)
open import Data.Integer' as ℤ using (ℤ ; +_ ; -suc_; [_]; ⌜_⌝)
  renaming (-_ to ℤ-_; _+_ to _ℤ+_; _-_ to _ℤ-_;_*_ to _ℤ*_;
  _≤_ to _ℤ≤_; _<_ to _ℤ<_; _◃_ to _ℤ◃_)
import Data.Integer.Properties' as ℤ
open import Data.Integer.Setoid renaming (_∼_ to _ℤ₀∼_; _-_ to _ℤ₀-_; _*_ to _ℤ₀*_)
open import Data.Rational' as ℚ₀

open import Relation.Binary.Core
open import Relation.Nullary.Core

infixl 8 _ℕ^_

lnz : ∀ {p q : Set} → ¬ p → ¬ (p × q)
lnz t (x , y) = t x

rnz : ∀ {p q : Set} → ¬ q → ¬ (p × q)
rnz t (x , y) = t y

_ℕ^_ : (a : ℕ) → (b : ℕ) → {p : ¬ (a ≡ 0 × b ≡ 0)} → ℕ
_ℕ^_ 0 0 {p} with p (refl , refl)
... | ()
0 ℕ^ suc b = 0
suc a ℕ^ 0 = suc 0
suc a ℕ^ suc b = suc a ℕ* (_ℕ^_ (suc a) b {lnz (λ ())})

infixl 8 _ℤ^ℕ_

_ℤ^ℕ_ : (a : ℤ) → (b : ℕ) → {p : ¬ (a ≡ + 0 × b ≡ 0)} → ℤ
_ℤ^ℕ_ (+ 0) 0 {p} with p (refl , refl)
... | ()
+ 0 ℤ^ℕ suc b = + 0
z ℤ^ℕ 0 = + suc 0
+ suc z ℤ^ℕ suc n = + suc z ℤ* (_ℤ^ℕ_ (+ suc z) n {lnz (λ ())})
-suc z ℤ^ℕ suc n = -suc z ℤ* (-suc z ℤ^ℕ n) {lnz (λ ())}

infixl 8 _ℤ÷_

_ℤ÷_ : (n : ℤ) → (d : ℤ) → {p : ℤ.¬0 d} → ℚ₀
_ℤ÷_ n (+ 0) {p} with p refl
... | ()
n ℤ÷ + suc d = n /suc d
n ℤ÷ -suc d = (ℤ- n) /suc d


_ℚ₀÷ℤ_ : (n : ℚ₀) → (d : ℤ) → {p : ℤ.¬0 d} → ℚ₀
_ℚ₀÷ℤ_ (n /suc d) (+ 0) {p} with p refl
... | ()
(n /suc d) ℚ₀÷ℤ (+ suc d') = n /suc (d d* d')
(n /suc d) ℚ₀÷ℤ (-suc d')  = ℤ- n /suc (d d* d')

infixl 8 _ℤ^_

_ℤ^_ : (a : ℤ) → (b : ℤ) → {p : ¬ (a ≡ + 0 × b ≡ + 0)} → ℚ₀
_ℤ^_ (+ 0) (+ 0) {p} with p (refl , refl)
... | ()
+ 0 ℤ^ a = qzero
a ℤ^ + 0 = qone
a ℤ^ + suc b = (_ℤ^ℕ_ a (suc b) {rnz (λ ())}) /suc 0
+ suc a ℤ^ -suc 0 = _ℤ÷_ (+ 1) (+ suc a) {λ ()}
+ suc a ℤ^ -suc suc b = _ℚ₀÷ℤ_ (_ℤ^_ (+ suc a)  (-suc b) {lnz (λ ())}) (+ suc a) {λ ()}
-suc a ℤ^ -suc 0 = _ℤ÷_ (+ 1) (-suc a) {λ ()}
-suc a ℤ^ -suc suc b = ((_ℤ^_ (-suc a) (-suc b) {lnz (λ ())}) ℚ₀÷ℤ (-suc a)) {λ ()} 

infixl 8 _ℤ^ℚ_

_ℤ^ℚ_ : (a : ℤ) → (b : ℚ₀) → {p : ¬ (a ≡ + 0 × (b ∼ qzero))} → ℚ₀
_ℤ^ℚ_ (+ 0) (+ 0 /suc d2) {p} with p (refl , refl)
... | () 
_ℤ^ℚ_ z (n2 /suc d2) with n2 ℤ- + suc d2
z ℤ^ℚ n2 /suc d2 | + 0 = z /suc 0
z ℤ^ℚ n2 /suc d2 | + suc n = _ℤ^_ z (+ suc n) {rnz (λ ())}
z ℤ^ℚ n2 /suc d2 | -suc n = (z ℤ^ -suc n) {rnz (λ ())}


infixl 8 _^_

lem1 : ∀ a b  → ℚ₀.¬0 (_ℤ^_ (+ suc a) (-suc b))
lem1 a b = {!a!}

lem2 : ∀ a b → (pa : ℤ.¬0 a) → (pb : ℤ.¬0 b) → ℚ₀.¬0 (_ℤ^_ a b {lnz pa})
lem2 a b pa pb = {!a!}

lem3 : ∀ {n} → + suc n ≢ + 0
lem3 ()

lem4 : ∀ {n} → -suc n ≢ + 0
lem4 ()

_^_ : (a : ℚ₀) → (b : ℚ₀) → {p : ¬ ((a ∼ qzero) × (b ∼ qzero))} → ℚ₀
_^_ (+ 0 /suc d1) ((+ 0) /suc d2) {p} with p (refl , refl)
... | ()
(+ 0) /suc d1 ^ _ = qzero
(+ suc n1) /suc d1 ^ n2 /suc d2 with n2 ℤ- + suc d2
(+ suc n1) /suc d1 ^ n2 /suc d2 | + ℕ.zero = (+ suc n1) /suc 0
(+ suc n1) /suc d1 ^ n2 /suc d2 | + suc n = 
  ((+ suc n1 ℤ^ (+ suc n)) {lnz (λ ())} ÷
  (+ suc d1 ℤ^ (+ suc n)) {lnz (λ ())})
  {lem2 (+ suc d1) (+ suc n) (λ()) (λ())}
(+ suc n1) /suc d1 ^ n2 /suc d2 | -suc n = 
  ((+ suc n1 ℤ^ (-suc n)) {lnz (λ ())} ÷
  (+ suc d1 ℤ^ (-suc n)) {lnz (λ ())})
  {lem1 d1 n }

(-suc n1) /suc d1 ^ n2 /suc d2 with n2 ℤ- + suc d2
(-suc n1) /suc d1 ^ n2 /suc d2 | + ℕ.zero = (-suc n1) /suc 0
(-suc n1) /suc d1 ^ n2 /suc d2 | + suc n =
  _÷_ (((-suc n1) ℤ^ (+ suc n)) {lnz (λ ())})
  (((+ suc d1) ℤ^ (+ suc n)) {lnz (λ ())})
  {lem2 (+ suc d1) (+ suc n) (λ ()) (λ ())}
(-suc n1) /suc d1 ^ n2 /suc d2 | -suc n = 
  _÷_ (((-suc n1) ℤ^ (-suc n)) {lnz (λ ())})
  (((+ suc d1) ℤ^ (-suc n)) {lnz (λ ())})
  {{!lem1 ? ?!} }

\end{code}