--------------------------------------------------
(ℤ, +, *, 0, 1) is a Commutative Ring

\begin{code}
module Data.Integer.Properties.CommutativeRing where

open import Algebra
open import Algebra.Structures
open import Function
open import Data.Product
open import Data.Integer'
open import Data.Integer.Setoid using (ℤ₀ ; _,_ ; _∼_) renaming (_+_ to _ℤ₀+_ ; -_ to ℤ₀-_; _*_ to _ℤ₀*_)
open import Data.Integer.Properties.BasicProp
open import Data.Integer.Setoid.Properties as ℤ₀ using (zrefl ; zsym ; _>∼<_)
import Data.Nat.Properties+ as ℕ
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
import Algebra.FunctionProperties as P; open P _≡_
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core
open import Symbols

\end{code}

1. + Identity

a) zero is left neutral (left identity) for addition
0 + z = z

b) zero is right neutral (right identity) for addition
z + 0 = z

\begin{code}

import Quotient.Lift as L
open  L ℤ-QuD

liftId : ∀ {op : Op 2 ℤ₀}(e : ℤ) → P.Identity _∼_ ⌜ e ⌝ op → Identity e (liftOp 2 op)
liftId {op} e (idl , idr) = (λ x → lift21' {op} e x x (idl ⌜ x ⌝)) , (λ x → lift21' {op} x e x (idr ⌜ x ⌝))
\end{code}

2. + Commutativity

m + n = n + m

\begin{code}

liftComm : ∀ {op : Op 2 ℤ₀} → P.Commutative _∼_ op → Commutative (liftOp 2 op)
liftComm {op} comm x y = sound $ comm ⌜ x ⌝ ⌜ y ⌝

\end{code}

3. + Associativity

(a + b) + c = a + (b + c)
\begin{code}


liftAssoc : ∀ {op : Op 2 ℤ₀}(cong : Cong2 op) → P.Associative _∼_ op → Associative (liftOp2safe op cong)
liftAssoc {op} cong assoc a b c = sound $ cong (compl {op ⌜ a ⌝ ⌜ b ⌝}) zrefl >∼< assoc ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ >∼< cong zrefl compl'

\end{code}

4. (_+_, -_, 0) Inverse

a) right inverse
x + (- x) = 0

\begin{code}

+neg : ∀ x y → x + (- y) ≡ x - y
+neg x y = sound $ ℤ₀.+-cong (zrefl {⌜ x ⌝}) compl >∼< ℤ₀.+neg ⌜ x ⌝ ⌜ y ⌝

+-rightInverse : RightInverse (+ 0) -_ _+_
+-rightInverse z = +neg z z >≡< sound (ℤ₀.-inverse ⌜ z ⌝)

\end{code}

b) left inverse
(- x) + x = 0

\begin{code}

+-leftInverse : LeftInverse (+ 0) -_ _+_
+-leftInverse z = cong (λ x → - z + x) ⟨ -inv {z} ⟩ >≡< +-rightInverse (- z)

+-inverse : Inverse (+ 0) -_ _+_
+-inverse = +-leftInverse , +-rightInverse

\end{code}


5. * Zero

a) 0 * z = 0

b) z * 0 = 0

\begin{code}

*-zero : Zero  (+ 0) _*_
*-zero = (λ x → sound (ℤ₀.0*z~0 ⌜ x ⌝)) , (λ x → sound (ℤ₀.z*0~0 ⌜ x ⌝))
-- 
\end{code}

6. * Identity

7. * Commutativity

a * b = b * a

8. * Assocciativity

(a * b) * c = a * (b * c)


9. * + Distributivity

a) left distributivity
a * (b + c) = a * b + a * c

\begin{code}

distˡ :  _*_ DistributesOverˡ _+_
distˡ a b c = sound $ ℤ₀.*-cong (zrefl {⌜ a ⌝}) compl >∼< 
                     ℤ₀.distˡ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ >∼< ℤ₀.+-cong compl' compl'

\end{code}

b) right distributivity
(b + c) * a = b * a + c * a

\begin{code}

distʳ : _*_ DistributesOverʳ _+_
distʳ a b c = sound $ ℤ₀.*-cong (compl {⌜ b ⌝ ℤ₀+ ⌜ c ⌝}) zrefl >∼< ℤ₀.distʳ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ >∼< ℤ₀.+-cong compl' compl'

distrib-*-+ : _*_ DistributesOver _+_
distrib-*-+ = distˡ , distʳ

\end{code} 

14. (ℤ, +, *, 0, 1) is a Commutative Ring

\begin{code}

liftMonoid : {op : Op 2 ℤ₀}{e : ℤ}(cong : Cong2 op) → IsMonoid _∼_ op  ⌜ e ⌝ → IsMonoid _≡_ (liftOp 2 op) e
liftMonoid {op} {e} cong im = record 
  { isSemigroup = record 
    { isEquivalence = isEquivalence
    ; assoc = liftAssoc cong (IsMonoid.assoc im)
    ; ∙-cong = cong₂ (liftOp 2 op)
    }
  ; identity = liftId {op} e (IsMonoid.identity im)
  }

isCommutativeRing : IsCommutativeRing _≡_ _+_ _*_ -_ (+ 0) (+ 1)
isCommutativeRing = record
  { isRing = record
    { +-isAbelianGroup = record
      { isGroup = record
        { isMonoid = liftMonoid (ℤ₀.+-cong) (IsCommutativeRing.+-isMonoid ℤ₀.isCommutativeRing)
        ; inverse = +-inverse
        ; ⁻¹-cong = cong -_
        }
        ; comm = liftComm ℤ₀.+-comm
     }
    ; *-isMonoid = liftMonoid (ℤ₀.*-cong) (IsCommutativeRing.*-isMonoid ℤ₀.isCommutativeRing)
    ; distrib = distrib-*-+
    }
  ; *-comm = liftComm ℤ₀.*-comm
  }

commutativeRing : CommutativeRing _ _
commutativeRing = record
  { _+_                   = _+_
  ; _*_                   = _*_
  ; -_                    = -_
  ; 0#                    = (+ 0)
  ; 1#                    = (+ 1)
  ; isCommutativeRing = isCommutativeRing
  }


\end{code}

15. The ring solver for ℤ

\begin{code}

import Algebra.RingSolver.Simple as Solver
import Algebra.RingSolver.AlmostCommutativeRing as ACR
module RingSolver =
  Solver (ACR.fromCommutativeRing commutativeRing)

\end{code}