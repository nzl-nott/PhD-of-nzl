\begin{code}

module Data.Nat.Properties+ where

open import Algebra
open import Algebra.Structures
open import Function
open import Data.Nat'
open import Data.Nat.Properties'
open import Data.Product
open import Relation.Binary
open import Relation.Binary.Core
open import Symbols

open module ℕ = IsCommutativeSemiring isCommutativeSemiring public hiding (refl ; zero)
module ℕO = DecTotalOrder decTotalOrder
 
infixr 42  _*⋆_
infixr 42  _⋆*_
infixl 41  _*=_
infixr 41  _+⋆_
infixr 41  _⋆+_
infixl 40 _>≤<_
infixl 40 _+=_

n+0≡n     : ∀ {n} → n + 0 ≡ n
n+0≡n {n} = proj₂ +-identity n

n+0≡n' : ∀ {n} n' m → n' ≡ n → m ≡ 0 → n' + m ≡ n
n+0≡n' {n} .n .0 refl refl = n+0≡n

n+0+0≡n : ∀ {n} → n + 0 + 0 ≡ n
n+0+0≡n {zero} = refl
n+0+0≡n {suc n} = suc ⋆ n+0+0≡n

n*0≡0 = proj₂ ℕ.zero

n*0+0=0 : ∀ {n} → n * 0 + 0 ≡ 0
n*0+0=0 {zero} = refl
n*0+0=0 {suc n} = n*0+0=0 {n}

n*1≡n = proj₂ *-identity

_*=_ : ∀ {a b c d} → a ≡ b → c ≡ d → a * c ≡ b * d
_*=_ = *-cong

_*⋆_ : ∀ a {b c} → b ≡ c → a * b ≡ a * c
_*⋆_ _ {b} {.b} refl = refl

_⋆*_ : ∀ {b c} → b ≡ c → (a : ℕ) →  b * a ≡ c * a
_⋆*_ {b} {.b} refl _ = refl

_>≤<_ : Transitive _≤_
_>≤<_ = ℕO.trans

_+=_ : ∀ {m n p q} → m ≡ n → p ≡ q → m + p ≡ n + q
_+=_ {m} {.m} {p} {.p} refl refl = refl

_+⋆_ : ∀ {p q} m → p ≡ q → m + p ≡ m + q
_+⋆_ _ refl = refl

_⋆+_ : ∀ {p q} → p ≡ q → (m : ℕ) → p + m ≡ q + m
_⋆+_ refl _ = refl

ex :  ∀ a b c → a + (b + c) ≡ b + (a + c)
ex a b c = ⟨ +-assoc a b c ⟩ >≡< +-comm a b ⋆+ c >≡< +-assoc b a c

exchange : ∀ m n p q → (m + n) + (p + q) ≡ (m + q) + (p + n)
exchange m n p q = +-assoc m n (p + q) >≡< m +⋆ ( ⟨ +-assoc n p q ⟩ >≡<
  (+-comm (n + p) q >≡<
  q +⋆ +-comm n p)) >≡<
  ⟨ +-assoc m q (p + n) ⟩

exchange₂ : ∀ m n p q → (m + n) + (p + q) ≡ (p + n) + (m + q)
exchange₂ m n p q = ⟨ +-assoc (m + n) p q ⟩ >≡< ((+-assoc m n p) >≡< 
  m +⋆ +-comm n p >≡< (+-comm m (p + n))) ⋆+ q >≡<
  +-assoc (p + n) m q

exchange₃ : ∀ m n p q → (m + n) + (p + q) ≡ (m + p) + (n + q)
exchange₃ m n p q = +-assoc m n (p + q) >≡<
  m +⋆ (ex n p q) >≡<
  ⟨ +-assoc m p (n + q) ⟩

exchange₄ : ∀ m n p q → (m + n) + (p + q) ≡ (m + p) + (q + n)
exchange₄ m n p q = +-assoc m n (p + q) >≡<
  m +⋆ (+-comm n (p + q) >≡< 
  +-assoc p q n) >≡<
  ⟨ +-assoc m p (q + n) ⟩

suc-elim      : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-elim refl = refl

suc-move           : ∀ m n → suc m + n ≡ m + suc n
suc-move zero n    = refl
suc-move (suc m) n = suc ⋆ (suc-move m n)

distˡ = proj₁ distrib

distʳ = proj₂ distrib

-- lemmas for *-assoc for setoid integer

dis2ˡ : ∀ a b c d e f → a * (b + c) + d * (e + f) ≡ (a * b + a * c) + (d * e + d * f) 
dis2ˡ a b c d e f = distˡ a b c += distˡ d e f

dis2ʳ : ∀ a b c d e f → (a + b) * c + (d + e) * f ≡ (a * c + b * c) + (d * f + e * f)
dis2ʳ  a b c d e f = distʳ c a b += distʳ f d e

*ass-lem : ∀ a b c d e f → 
  (a * c + b * d) * e + (a * d + b * c) * f ≡ a * (c * e + d * f) + b * (c * f + d * e)
*ass-lem a b c d e f = 
  dis2ʳ (a * c) (b * d) e (a * d) (b * c) f >≡< 
  exchange₄ (a * c * e) (b * d * e) (a * d * f) (b * c * f) >≡< 
  (*-assoc a c e += *-assoc a d f += (*-assoc b c f += *-assoc b d e)) >≡< 
  ⟨ dis2ˡ a (c * e) (d * f) b (c * f) (d * e) ⟩

dist-lemˡ : ∀ a b c d e f → a * (c + e) + b * (d + f) ≡ (a * c + b * d) + (a * e + b * f) 
dist-lemˡ a b c d e f = dis2ˡ a c e b d f >≡< exchange₃ (a * c) (a * e) (b * d) (b * f)  

dist-lemʳ : ∀ a b c d e f → (c + e) * a + (d + f) * b ≡ (c * a + d * b) + (e * a + f * b) 
dist-lemʳ a b c d e f = dis2ʳ c e a d f b >≡< exchange₃ (c * a) (e * a) (d * b) (f * b)  

distˡʳ : ∀ a b c → a * (b + c) ≡ b * a + c * a
distˡʳ a b c = *-comm a (b + c) >≡< distʳ a b c

*-cong-lem₁ : ∀ a b c d e f g h → 
  a + b + (c + d) + (e + f + (g + h)) ≡ a + d + (f + g) + (b + c + (e + h))
*-cong-lem₁ a b c d e f g h = exchange a b c d += exchange₂ e f g h >≡< 
  (exchange₃ (a + d) (c + b) (g + f) (e + h) >≡< 
  ((a + d) +⋆ +-comm g f += +-comm c b ⋆+ (e + h)))

*-cong-lem₂ : ∀ a b c d e f g h → 
  a + b + (c + d) + ((e + f) + (g + h)) ≡ e + h + (c + b) + ((g + f) + (a + d))
*-cong-lem₂ a b c d e f g h = exchange a b c d += exchange e f g h >≡< 
  exchange₂ (a + d) (c + b) (e + h) (g + f) 
  >≡< (e + h + (c + b)) +⋆ +-comm (a + d) (g + f)


+l-cancel : ∀ x {m n} → x + m ≡ x + n → m ≡ n
+l-cancel = cancel-+-left

+l-cancel' : ∀ {m n x y} → x ≡ y → x + m ≡ y + n → m ≡ n
+l-cancel' {m} {n} {x} {.x} refl eqt = cancel-+-left x eqt

+r-cancel : ∀ {m n} x → m + x ≡ n + x → m ≡ n
+r-cancel {m} {n} x eqt =  cancel-+-left x $ +-comm x m >≡< eqt >≡< +-comm n x

_+suc_≢0_ : ∀ m n → m + suc n ≢ 0
0 +suc n ≢0 ()
(suc m) +suc n ≢0 ()

sucn≢n       : ∀ n → suc n ≢ n
sucn≢n zero ()
sucn≢n (suc n) eqt = sucn≢n n (suc-elim eqt)

sucn≢0 : ∀ {n} → suc n ≢ 0
sucn≢0 ()

*suc : ∀ a b → a * suc b ≡ a + a * b
*suc a b = *-comm a (suc b) >≡< a +⋆ *-comm b a

suc*move : ∀ a b → a + (suc a) * b ≡ b + a * suc b
suc*move  a b = +-comm a (b + a * b) >≡< +-assoc b (a * b) a >≡< b +⋆ (+-comm (a * b) a >≡< ⟨ *suc a b ⟩)


*-ex :  ∀ a b c → a * (b * c) ≡ b * (a * c)
*-ex a b c = ⟨ *-assoc a b c ⟩ >≡< *-comm a b ⋆* c >≡< *-assoc b a c


*-exchange₃ : ∀ m n p q → (m * n) * (p * q) ≡ (m * p) * (n * q)
*-exchange₃ m n p q = *-assoc m n (p * q) >≡<
  m *⋆ (*-ex n p q) >≡<
  ⟨  *-assoc m p (n * q) ⟩

\end{code}

Integrity

\begin{code}

integrity : ∀ a {m n} → (suc a) * m ≡ (suc a) * n → m ≡ n
integrity a {m} {n}               a*≡ = cancel-*-right m n (*-comm m (suc a) >≡< a*≡ >≡< *-comm (suc a) n)

refl′ : _≡_ ⇒ _≤_
refl′ = ℕO.reflexive

+l-cancel′ : ∀ a {b c} → a + b ≤ a + c → b ≤ c
+l-cancel′ zero ue = ue
+l-cancel′ (suc n) (s≤s b≤c) = +l-cancel′ n b≤c

_+⋆′_ : ∀ {a b} c → a ≤ b → c + a ≤ c + b
zero +⋆′ a≤b = a≤b
suc n +⋆′ a≤b = s≤s (n +⋆′ a≤b)


_+≤_ : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
_+≤_ {.0} {b} {c} {d} z≤n c≤d = ≤-steps b c≤d
_+≤_ {.(suc a)} {.(suc b)} {c} {d} (s≤s {a} {b} a≤b) c≤d = s≤s (_+≤_ {a} {b} {c} {d} a≤b c≤d)


l-≤resp : ∀ {a b n} → a ≡ b → n ≤ a → n ≤ b
l-≤resp = proj₁ ℕO.≤-resp-≈

r-≤resp : ∀ {a b n} → a ≡ b → a ≤ n → b ≤ n
r-≤resp = proj₂ ℕO.≤-resp-≈


*-cong′ : ∀ {m n} c →  m ≤ n → c * m ≤ c * n
*-cong′ zero m≤n = z≤n
*-cong′ {m} {n} (suc c) m≤n = m≤n +≤ *-cong′ c m≤n


i′-lem : ∀ {m} n → m ≤ n * 0 → m ≤ 0
i′-lem n = l-≤resp (n*0≡0 n)

integrity′ : ∀ {a b} c →(suc c) * a ≤ (suc c) * b → a ≤ b
integrity′ {zero}  {b} c ue = z≤n
integrity′ {suc a} {zero} c ue with i′-lem c ue
integrity′ {suc a} {zero} c ue | ()
integrity′ {suc a} {suc b} c (s≤s m≤n) = 
  s≤s $
  integrity′ c $
  +l-cancel′ c $
  l-≤resp (⟨ suc*move c b ⟩) $
  r-≤resp (⟨ suc*move c a ⟩) m≤n

ℤ₀i-lem : ∀ a b c → a + b + c * (a + b) ≡ a + c * a + (b + c * b)
ℤ₀i-lem a b c = (a + b) +⋆ distˡ c a b >≡< exchange₃ a b (c * a) (c * b)

ℤ₀i-lem₁ : ∀ a b c → a + c * a + 0 + (b + c * b + 0) ≡ a + b + c * (a + b)
ℤ₀i-lem₁ a b c = n+0≡n {a + c * a} += n+0≡n >≡< ⟨ ℤ₀i-lem a b c ⟩

ℤ₀i-lem₂ : ∀ a b c → a + b + c * (a + b) ≡ b + c * b + (a + c * a)
ℤ₀i-lem₂ a b c = ℤ₀i-lem a b c >≡< +-comm (a + c * a) (b + c * b)
\end{code}