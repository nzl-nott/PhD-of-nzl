
\AgdaHide{
\begin{code}

module QInteger where


open import Data.Nat
open import Data.Product
open import Function
open import Data.Nat.Properties
open import Nat.Properties+
open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import Relation.Binary hiding (Setoid)

open import Symbols
open import Setoids
open import Quotient
\end{code}
}

\section{Integers}

Base set of setoid Integer

\begin{code}
infix 4 _,_

data ℤ₀ : Set where
  _,_ : ℕ → ℕ → ℤ₀
\end{code}

Equivalence relation

\begin{code}
infixl 2 _∼_

_∼_ : ℤ₀ → ℤ₀ → Set
(x+ , x-) ∼ (y+ , y-) = (x+ + y-) ≡ (y+ + x-)
\end{code}

Equivalence properties

\begin{code}
∼refl : ∀ {a} → a ∼ a
∼refl {x+ , x-} = refl

∼sym : ∀ {a b} → a ∼ b → b ∼ a
∼sym {x+ , x-} {y+ , y-} = sym

∼trans :  ∀ {a b c} → a ∼ b → b ∼ c → a ∼ c
∼trans {x+ , x-} {y+ , y-} {z+ , z-} x=y y=z = 
       cancel-+-left (y+ + y-) 
       (swap24 y+ y- x+ z- 
       >≡< ((y=z += x=y) >≡< swap13 z+ y- y+ x-))

_∼_isEquivalence : IsEquivalence _∼_
_∼_isEquivalence = record
  { refl  = ∼refl
  ; sym   = ∼sym
  ; trans = ∼trans
  }
\end{code}

(ℤ₀, ∼) is a setoid

\begin{code}
ℤ-Setoid : Setoid
ℤ-Setoid = record
  { Carrier       = ℤ₀
  ; _~_           = _∼_
  ; isEquivalence = _∼_isEquivalence
  }
\end{code}

We use the definition of $\Z$ in standard library
\begin{code}
open import Data.Integer hiding (_+_; pred) 
  renaming (-[1+_] to -suc_)
\end{code}

Normalisation function

\begin{code}
[_]                   : ℤ₀ → ℤ
[ m , 0 ]             = + m
[ 0 , suc n ]       = -suc n
[ suc m , suc n ] = [ m , n ]
\end{code}

Embedding function

\begin{code}
⌜_⌝        : ℤ → ℤ₀
⌜ + n ⌝    = n , 0
⌜ -suc n ⌝ = 0 , ℕ.suc n
\end{code}

Stability

\begin{code}

stable            : ∀ {n} → [ ⌜ n ⌝ ] ≡ n
stable {+ n}      = refl
stable { -suc n } = refl

\end{code}

Completeness

\begin{code}

compl : ∀ n → ⌜ [ n ] ⌝ ∼ n
compl (x , 0)         = refl
compl (0 , suc y)     = refl
compl (suc x , suc y) = ∼trans (compl (x , y)) 
                          (sym (sm+n≡m+sn x))


sound' : ∀ {i j} → ⌜ i ⌝ ∼ ⌜ j ⌝  → i ≡ j
sound'  {+ i} {+ j} eqt      = +_ ⋆ (+r-cancel 0 eqt)
sound'  {+ i} { -suc j } eqt with i +suc j ≢0 eqt
... | ()
sound'  { -suc i } { + j } eqt with j +suc i ≢0 ⟨ eqt ⟩
... | ()
sound'  { -suc i } { -suc j } eqt = -suc_ ⋆ pred ⋆ ⟨ eqt ⟩
\end{code}

Soundness

\begin{code}
sound : ∀ {x y} → x ∼ y → [ x ] ≡ [ y ]
sound { x } { y } x∼y = sound' (∼trans (compl _) 
      (∼trans (x∼y) (∼sym (compl _)))) 
\end{code}

The quotient definitions for ℤ

\begin{code}
ℤ-PreQu : pre-Quotient ℤ-Setoid
ℤ-PreQu = record
  { Q       = ℤ
  ; [_]     =  [_]
  ; [_]⁼   = sound
  }

ℤ-QuD : def-Quotient ℤ-PreQu
ℤ-QuD = record
  { emb       = ⌜_⌝
  ; complete  = λ z → compl _
  ; stable    = λ z → stable
  }

ℤ-Qu = def-Quotient→Quotient ℤ-QuD
\end{code}
