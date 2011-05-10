--------------------------------------------------
The basic properties of integers

\begin{code}

module Data.Integer.Properties.BasicProp where

open import Function
open import Data.Nat using (ℕ) renaming (suc to nsuc; pred to npre)
open import Data.Product
open import Data.Sign as Sign using (Sign)
open import Data.Integer'
open import Data.Integer.Setoid using (_∼_)
  renaming (_+_ to _ℤ₀+_; _◃_ to _ℤ₀◃_; _*_ to _ℤ₀*_; -_ to ℤ₀-_
  ; _≤_ to _ℤ₀≤_; ¬0 to ℤ₀¬0)
open import Data.Integer.Setoid.Properties as ℤ₀
  using (zrefl ; zsym ; _>∼<_ ; ℤ-Setoid; refl') 
  renaming (_≟_ to _ℤ₀≟_ ; _≤?_ to _ℤ₀≤?_)
open import Data.Nat.Properties+ as ℕ using (_+suc_≢0_)

open import Quotient

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core
open import Symbols

module ℤ₀O = DecTotalOrder ℤ₀.decTotalOrder

infixl 40 _>≤<_

ℤ₀l-≤resp : ∀ {n x y} → x ∼ y → n ℤ₀≤ x → n ℤ₀≤ y
ℤ₀l-≤resp = proj₁ ℤ₀O.≤-resp-≈

ℤ₀r-≤resp : ∀ {n x y} → x ∼ y → x ℤ₀≤ n → y ℤ₀≤ n
ℤ₀r-≤resp = proj₂ ℤ₀O.≤-resp-≈

\end{code}

p is left inverse of i
p ∘ i = ℕid

\begin{code}

invertibility   : ∀ n → p (i n)  ≡ n
invertibility n = refl

\end{code}

disjoint:
0 and positive number is not equal to negative number

\begin{code}

+≠- : ∀ {x y} → + x ≢ -suc y
+≠- ()

\end{code}

small lemma that transform the non-zero condition for ℤ to the one for ℤ₀

\begin{code}

⌜nz⌝ : ∀ {a} → ¬0 a → ℤ₀¬0 ⌜ a ⌝
⌜nz⌝ {+ n} p     = λ n≡0 → p (+_ ⋆ n≡0)
⌜nz⌝ { -suc n} p = λ ()

\end{code}

a) stability:
nf is left inverse of dn

\begin{code}

stable            : ∀ {n} → [ ⌜ n ⌝ ] ≡ n
stable {+ n}      = refl
stable { -suc n } = refl

\end{code}

b) completeness:
if it is true, then we can give the proof

\begin{code}

compl                   : ∀ {n} → ⌜ [ n ] ⌝ ∼ n
compl {x , 0}           = refl
compl {0 , nsuc y}      = refl
compl {nsuc x , nsuc y} = compl {x , y} >∼<  ⟨ ℕ.sm+n≡m+sn x y ⟩

compl' : ∀ {n} → n ∼  ⌜ [ n ] ⌝
compl' = zsym compl

⌞_⌟          : ∀ {i j} → ⌜ i ⌝ ∼ ⌜ j ⌝  → i ≡ j
⌞_⌟  {+ i} {+ j} eqt      = +_ ⋆ (ℕ.+r-cancel 0 eqt)
⌞_⌟  {+ i} { -suc j } eqt with i +suc j ≢0 eqt
... | ()
⌞_⌟  { -suc i } { + j } eqt with j +suc i ≢0 ⟨ eqt ⟩
... | ()
⌞_⌟  { -suc i } { -suc j } eqt = -suc_ ⋆ npre ⋆ ⟨ eqt ⟩

\end{code}

c) soundness:
if we proved it, then it is true

Note: b) and c) proves that ∼ and nf∼ define the same equivalence relation on ℤ₀

\begin{code}

sound                 : ∀ {x y} → x ∼ y → [ x ] ≡ [ y ]
sound { x } { y } x∼y = ⌞ compl >∼< x∼y >∼< compl' ⌟ 

\end{code}

c) The quotient definition for ℤ

\begin{code}

ℤ-QuSig : QuSig ℤ-Setoid
ℤ-QuSig = record
  { Q       = ℤ
  ; [_]     = [_]
  ; sound   = sound
  }

ℤ-Nf : Nf ℤ-QuSig
ℤ-Nf = record
  { emb       = ⌜_⌝
  ; compl     = λ z → compl
  ; stable    = λ z → stable
  }

ℤ-Qu = nf2qu ℤ-Nf

ℤ-QuE = nf2quE {_} {_} {ℤ-Qu} ℤ-Nf

complete : ∀ {a b} → [ a ] ≡ [ b ] → a ∼ b
complete = QuE.complete ℤ-QuE

\end{code}

Properties about sign functions

\begin{code}
sign◃ : ∀ m → sign m ◃ p m ≡ m
sign◃ (+ n) = refl
sign◃ (-suc n) = refl

◃-cong : ∀ {m n} → sign m ≡ sign n → p m ≡ p n → m ≡ n
◃-cong {m} {n} sign-≡ abs-≡ = ⟨ sign◃ m ⟩ >≡<
  cong₂ _◃_ sign-≡ abs-≡ >≡< sign◃ n

infix 5 _◂_

data SignAbs : ℤ → Set where
  _◂_ : (s : Sign) (n : ℕ) → SignAbs (s ◃ n)

signAbs : ∀ m → SignAbs m
signAbs m = subst SignAbs (sign◃ m) $ sign m ◂ (p m)

absSign : ∀ s n → p (s ◃ n) ≡ n
absSign Sign.- 0        = refl
absSign Sign.- (nsuc n) = refl
absSign Sign.+ n        = refl

\end{code}

The integrity of ℤ

\begin{code}

+compl : ∀ m n → ⌜ m + n ⌝ ∼ ⌜ m ⌝ ℤ₀+ ⌜ n ⌝
+compl m n = compl

\end{code}

Helpful functions for the proving the properties of rational numbers

\begin{code}

[-out]     : ∀ a → [ ℤ₀- a ] ≡ - [ a ]
[-out] (0 , 0)           = refl
[-out] (0 , nsuc n)      = refl
[-out] (nsuc m , 0)      = refl
[-out] (nsuc m , nsuc n) = [-out] (m , n)

-inv : ∀ {z} → - - z ≡ z
-inv {+ 0} = refl
-inv {+ nsuc n} = refl
-inv { -suc n} = refl

-out         : ∀ a b → (- a) * b ≡ - (a * b) 
-out a b     = sound (ℤ₀.*-cong compl zrefl >∼<
  (ℤ₀.-out ⌜ a ⌝ ⌜ b ⌝)) >≡< [-out] (⌜ a ⌝ ℤ₀* ⌜ b ⌝)


\end{code}

_≡_, is0 and _≤_ are decidable_

\begin{code}

_≟_   : Decidable _≡_
m ≟ n with ⌜ m ⌝ ℤ₀≟ ⌜ n ⌝
_ ≟ _    | yes p = yes ⌞ p ⌟
_ ≟ _    | no ¬p = no $ ¬p ∘ refl' ∘ cong ⌜_⌝

0?   : ∀ z → Dec (is0 z)
0? (+ 0)      = yes refl
0? (+ nsuc n) = no (λ ())
0? (-suc n)   = no (λ ())

¬0? : ∀ z → Dec (¬0 z)
¬0? (+ 0) = no (λ x → x refl)
¬0? (+ nsuc n) = yes (λ ())
¬0? (-suc n) = yes (λ ())

_≤?_ : Decidable _≤_
a ≤? b = ⌜ a ⌝ ℤ₀≤? ⌜ b ⌝

\end{code}

(ℤ, =, ≤) is a total order

\begin{code}

refl′ :  _≡_ ⇒ _≤_
refl′ refl = ℤ₀O.reflexive zrefl 

antisym : Antisymmetric _≡_ _≤_
antisym m n = ⌞ ℤ₀O.antisym m n ⌟

total : Total _≤_
total a b = ℤ₀O.total ⌜ a ⌝ ⌜ b ⌝

decTotalOrder : DecTotalOrder _ _ _
decTotalOrder = record
  { Carrier         = ℤ
  ; _≈_             = _≡_
  ; _≤_             = _≤_
  ; isDecTotalOrder = record
      { isTotalOrder = record
          { isPartialOrder = record
              { isPreorder = record
                  { isEquivalence = isEquivalence
                  ; reflexive     = refl′
                  ; trans         = ℤ₀O.trans
                  ; ∼-resp-≈      = resp₂ _≤_
                  }
              ; antisym  = antisym
              }
          ; total = total
          }
      ; _≟_  = _≟_
      ; _≤?_ = _≤?_
      }
  }


\end{code}

symbols for transitivity of ≤

\begin{code}

_>≤<_ : Transitive _≤_
_>≤<_  = ℤ₀O.trans

+compl≤ : ∀ {a b} → ⌜ [ a ] ⌝ ℤ₀≤ ⌜ [ b ] ⌝ → a ℤ₀≤ b
+compl≤ = ℤ₀r-≤resp compl ∘ ℤ₀l-≤resp compl

+compl≤' : ∀ {a b} → a ℤ₀≤ b → ⌜ [ a ] ⌝ ℤ₀≤ ⌜ [ b ] ⌝
+compl≤' = ℤ₀r-≤resp compl' ∘ ℤ₀l-≤resp compl'

\end{code}

+ preserves ≤

\begin{code}

+-pres₂′ : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
+-pres₂′ a≤b = +compl≤' ∘ ℤ₀.+-pres₂′ a≤b

\end{code}

* preserves ≤ for non-negative integers

\begin{code}

*-pres′ : ∀ {a b} n → a ≤ b → (+ n) * a ≤ (+ n) * b
*-pres′ n = +compl≤' ∘ ℤ₀.*-pres′ n

\end{code}

+ cancellation for ≤ 

\begin{code}

+-cancel′ : ∀ a {b c} → a + b ≤ a + c → b ≤ c
+-cancel′ a = ℤ₀.+l-cancel′ ⌜ a ⌝ ∘ +compl≤

\end{code}

integrity for ≤ 

\begin{code}

integrity′ : ∀ {a b} c → + nsuc c * a ≤ + nsuc c * b → a ≤ b
integrity′ c = ℤ₀.integrity′ c ∘ +compl≤

\end{code}
