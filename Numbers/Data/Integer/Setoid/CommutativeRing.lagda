--------------------------------------------------
(ℤ₀, ∼, +, *, 0, 1) is a Commutative Ring

note: Because [0 , 0]₌ ∼ (0 , 0), (0 , 0) represents 0 and (1 , 0) represents 1.

\begin{code}
module Data.Integer.Setoid.CommutativeRing where

open import Algebra 
open import Algebra.Structures
open import Data.Integer.Setoid 
open import Data.Integer.Setoid.BasicProp  
open import Data.Nat using () renaming (_+_ to _ℕ+_ ;  _*_ to _ℕ*_)
open import Data.Nat.Properties+ as ℕ using (_+=_; _*⋆_)
open import Data.Product
open import Relation.Binary.Core 
import Algebra.FunctionProperties as P; open P _∼_
open import Symbols


\end{code}

1. + Identity

a) zero is left neutral (left identity) for addition
0 + z = z

\begin{code}

0+z~z : LeftIdentity (0 , 0) _+_
0+z~z (x+ , x-) = refl

\end{code}

b) zero is right neutral (right identity) for addition
z + 0 = z

\begin{code}

z+0~z : RightIdentity (0 , 0) _+_
z+0~z (a , b) = ℕ.n+0≡n {a} += ⟨ ℕ.n+0≡n ⟩

\end{code}

c) + identity

\begin{code}

+-identity : Identity (0 , 0) _+_
+-identity = 0+z~z , z+0~z

\end{code}

2. + Commutativity

a + b ~ b + a

\begin{code}

+-comm : Commutative _+_
+-comm (x+ , x-) (y+ , y-) = (ℕ.+-comm x+ y+) += (ℕ.+-comm y- x-)

\end{code}

3. + Associativity

(a + b) + c ~ a + (b + c)

\begin{code}

+-assoc : Associative _+_
+-assoc (x+ , x-) (y+ , y-) (z+ , z-) =
  (ℕ.+-assoc x+ y+ z+) += ⟨ ℕ.+-assoc x- y- z- ⟩

\end{code}

4. (_+_, -_, 0) Inverse

a) x + (- x) ~ 0

\begin{code}

+neg : ∀ x y → x + (- y) ∼ x - y
+neg (x+ , x-) (y+ , y-) = refl

-inverse : ∀ x → x - x ∼ (0 , 0)
-inverse (x+ , x-) = ℕ.+-comm (x+ ℕ+ x-) 0 >≡<
  ℕ.+-comm x+ x-

+-rightInverse : RightInverse (0 , 0) -_ _+_
+-rightInverse (x+ , x-) = -inverse (x+ , x-)

\end{code}

b) (- x) + x ~ 0

\begin{code}

+-leftInverse : LeftInverse (0 , 0) -_ _+_
+-leftInverse (x+ , x-) = +-rightInverse (x- , x+)

+-inverse : Inverse (0 , 0) -_ _+_
+-inverse = +-leftInverse , +-rightInverse

\end{code}

5. * zero

a) 0 * a ~ 0

\begin{code}

0*z~0 : LeftZero (0 , 0) _*_
0*z~0 (x+ , x-) = refl

\end{code}

b) a * 0 ~ 0

\begin{code}

z*0~0 : RightZero (0 , 0) _*_
z*0~0 (x+ , x-) =  ℕ.n+0≡n

*-zero : Zero  (0 , 0) _*_
*-zero = 0*z~0 , z*0~0

\end{code}

6. * identity

a) left identity
1 * a ~ a

\begin{code}

1*z~z : LeftIdentity (1 , 0) _*_
1*z~z (x+ , x-) =  ℕ.n+0+0≡n {x+} += ⟨  ℕ.n+0+0≡n ⟩

\end{code}

b) right identity
a * 1 ~ a

\begin{code}

z*1~z : RightIdentity (1 , 0) _*_
z*1~z (x+ , x-) =
  ( ℕ.n*1≡n x+ +=  ℕ.n*0≡0 x- >≡<  ℕ.n+0≡n {x+}) +=
  ⟨  ℕ.n*0≡0 x+ +=  ℕ.n*1≡n x- ⟩ 

*-identity : Identity (1 , 0) _*_
*-identity = 1*z~z , z*1~z

\end{code}

7. * commutativity

a * b ~ b * a

\begin{code}

*-comm :  Commutative _*_
*-comm (x+ , x-) (y+ , y-) = 
  ℕ.*-comm x+ y+ += ℕ.*-comm x- y- +=
  (ℕ.+-comm (y+ ℕ* x-) (y- ℕ* x+) >≡< 
  (ℕ.*-comm y- x+ += ℕ.*-comm y+ x-))

\end{code}

8. * assocciativity

(a * b) * c ~ a * (b * c)

\begin{code}

*-assoc : Associative _*_
*-assoc (a , b) (c , d) (e , f) = 
  ℕ.*ass-lem a b c d e f +=
  ⟨  ℕ.*ass-lem a b c d f e ⟩

\end{code}

9. * + distributivity

a) left distributivity

a * (b + c) ~ a * b + a * c

\begin{code}

distˡ :  _*_ DistributesOverˡ _+_
distˡ (a , b) (c , d) (e , f) = 
  ℕ.dist-lemˡ a b c d e f +=
  ⟨  ℕ.dist-lemˡ a b d c f e ⟩

\end{code}

b) right distributivity

(b + c) * a ~ b * a + c * a

\begin{code}

distʳ : _*_ DistributesOverʳ _+_
distʳ (a , b) (c , d) (e , f) =
  ℕ.dist-lemʳ a b c d e f +=
  ⟨  ℕ.dist-lemʳ b a c d e f ⟩

distrib-*-+ : _*_ DistributesOver _+_
distrib-*-+ = distˡ , distʳ

\end{code}

10. + preserves ∼

∀ a b c d → a ~ b → c ~ d → a + c ~ b + d

\begin{code}

+-cong : ∀ {x y u v} → x ∼ y → u ∼ v → x + u ∼ y + v
+-cong {a , b} {c , d} {e , f} {g , h} x∼y u∼v = 
  ℕ.exchange₃ a e d h >≡<
  (x∼y += u∼v) >≡<
  ℕ.exchange₃ c b g f

\end{code}

11. -_ preserves ∼

∀ a b → a ~ b → - a ~ - b

\begin{code}

⁻¹-cong : ∀ {x y} → x ∼ y → - x ∼ - y
⁻¹-cong {a , b} {c , d} eqt = ℕ.+-comm b c >≡< ⟨ eqt ⟩ >≡<
  ℕ.+-comm a d

\end{code}

12. * preserves ∼

∀ a b c d → a ~ b → c ~ d → a * c ~ b * d

\begin{code}

*-cong : ∀ {x y u v} → x ∼ y → u ∼ v → x * u ∼ y * v
*-cong {a , b} {c , d} {e , f} {g , h} eqt1 eqt2 = 
   ℕ.+r-cancel (d ℕ* e ℕ+ c ℕ* f ℕ+ (c ℕ* e ℕ+ d ℕ* f))
  (⟨  ℕ.distˡʳ e a d +=  ℕ.distˡʳ f c b +=
  (ℕ.distˡ c e h += ℕ.distˡ d g f) >≡< 
  ℕ.*-cong-lem₁ (a ℕ* e) (d ℕ* e) (c ℕ* f) (b ℕ* f) (c ℕ* e)
  (c ℕ* h) (d ℕ* g) (d ℕ* f) ⟩ >≡< 
  (e *⋆ eqt1 += f *⋆ ⟨ eqt1 ⟩ += (c *⋆ eqt2 += d *⋆ ⟨ eqt2 ⟩)) >≡< 
  ( ℕ.distˡʳ e c b += ℕ.distˡʳ f a d +=
  (ℕ.distˡ c g f += ℕ.distˡ d e h)) >≡<
   ℕ.*-cong-lem₂ (c ℕ* e) (b ℕ* e) (a ℕ* f) (d ℕ* f) (c ℕ* g)
  (c ℕ* f) (d ℕ* e) (d ℕ* h))

\end{code}

13. (ℤ₀, ∼, +, *, 0, 1) is Commutative Ring

\begin{code}

isCommutativeRing : IsCommutativeRing _∼_ _+_ _*_ -_ (0 , 0) (1 , 0)
isCommutativeRing = record
  { isRing = record
    { +-isAbelianGroup = record
      { isGroup = record
        { isMonoid = record
          { isSemigroup = record
            { isEquivalence = _∼_isEquivalence
            ; assoc         = +-assoc
            ; ∙-cong      = +-cong
            }
          ; identity = +-identity
          }
        ; inverse = +-inverse
        ; ⁻¹-cong = ⁻¹-cong
        }
        ; comm = +-comm
     }
    ; *-isMonoid = record
        { isSemigroup = record
          { isEquivalence = _∼_isEquivalence
          ; assoc         = *-assoc
          ; ∙-cong      = *-cong
          }
        ; identity = *-identity
        }
    ; distrib = distrib-*-+
    }
  ; *-comm = *-comm
  }

commutativeRing : CommutativeRing _ _
commutativeRing = record
  { _+_                   = _+_
  ; _*_                   = _*_
  ; -_                    = -_
  ; 0#                    = (0 , 0)
  ; 1#                    = (1 , 0)
  ; isCommutativeRing = isCommutativeRing
  }

\end{code}

14. The ring solver for ℤ₀
It can be used to solve simple propositions of ℤ₀
\begin{code}

import Algebra.RingSolver.Simple as Solver
import Algebra.RingSolver.AlmostCommutativeRing as ACR
module RingSolver =
  Solver (ACR.fromCommutativeRing commutativeRing)

\end{code}

