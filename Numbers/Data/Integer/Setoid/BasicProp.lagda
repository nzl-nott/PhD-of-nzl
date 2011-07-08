--------------------------------------------------
The basic properties of setoid integers

\begin{code}
module Data.Integer.Setoid.BasicProp where

open import Algebra
open import Algebra.Structures
open import Data.Integer.Setoid
open import Function using (_$_ ; _∘_)
open import Data.Nat hiding (decTotalOrder) 
  renaming (_≟_ to _ℕ≟_; _+_ to _ℕ+_; _*_ to _ℕ*_ ;
  _≤?_ to _ℕ≤?_; _≤_ to _ℕ≤_)
open import Data.Nat.Properties
open import Data.Nat.Properties+ as ℕ+ hiding (+l-cancel′ ; integrity′ ; sym ; _>≤<_)
open import Data.Product hiding (proj₁)
open import Data.Sign as Sign using (Sign)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE
open import Relation.Nullary.Core
open import Symbols



infixl 40 _>∼<_

\end{code}

- is inverse to itself

\begin{code}

-inv : ∀ {x} → - - x ∼ x
-inv {x+ , x-} = refl

\end{code}

p is left inverse of i : p ∘ i = idℕ

\begin{code}

invertibility   : ∀ n → p (i n)  ≡ n
invertibility n = refl

\end{code}

- congruence

\begin{code}

-cong : ∀ {x y} → x ∼ y → - x ∼ - y
-cong {a , b} {c , d} eqt = +-comm b c >≡< ⟨ eqt ⟩ >≡< +-comm a d

\end{code}

move the '-' out of multiplication
(- 1) * 3 = - (1 * 3)
helpful lemma for proving the properties of ℚ₀

\begin{code}

-out : ∀ x y → - x * y ∼ - (x * y)
-out (a , b) (c , d) = (+-comm (b ℕ* c) (a ℕ* d)) +=
                         (+-comm (a ℕ* c) (b ℕ* d))

\end{code}

The '∼' is equivalence

a) reflexivity: ∀ a → a ∼ a

\begin{code}

zrefl : Reflexive _∼_
zrefl {x+ , x-} = refl

\end{code}

b) symmetry: ∀ a b → a ∼ b → b ∼ a

\begin{code}

zsym : Symmetric _∼_
zsym {x+ , x- } {y+ , y- } = sym

\end{code}

c) transitivity:  ∀ a b c → a ∼ b /\ b ∼ c → a ∼ c
(the symbol is easier for use)

\begin{code}

_>∼<_ : Transitive _∼_
_>∼<_ { x+ , x- } { y+ , y- } { z+ , z- } x=y y=z =
  cancel-+-left (y+ ℕ+ y-) $ exchange₁ y+ y- x+ z- >≡<
  (y=z += x=y) >≡< exchange₂ z+ y- y+ x-

\end{code}

d) Combine these 3 propertiese we can prove that '∼' is equivalence

\begin{code}

_∼_isEquivalence : IsEquivalence _∼_
_∼_isEquivalence = record
  { refl  = zrefl
  ; sym   = zsym
  ; trans = _>∼<_
  }

\end{code}

(ℤ₀, ∼) is a setoid

\begin{code}

ℤ-Setoid : Setoid _ _
ℤ-Setoid = record
  { Carrier       = ℤ₀
  ; _≈_           = _∼_
  ; isEquivalence = _∼_isEquivalence
  }

\end{code}

_∼_, is0 and ¬0 are decidable

\begin{code}

infix 2 _≟_

_≟_   : Decidable _∼_
(x+ , x-) ≟ (y+ , y-) = (x+ ℕ+ y-) ℕ≟ (y+ ℕ+ x-)

0? : ∀ z → Dec (is0 z)
0? (0 , 0)       = yes refl
0? (0 , suc _) = no (λ ())
0? (suc _ , 0) = no (λ ())
0? (suc a , suc b) with 0? (a , b)
0? (suc .b , suc b) | yes refl = yes refl
0? (suc a , suc b)  | no ¬p    = no (λ a≡b → ¬p (pred ⋆ a≡b))

¬0? : ∀ z → Dec (¬0 z)
¬0? z with 0? z
¬0? z | yes p = no (λ x → x p)
¬0? z | no ¬p = yes ¬p

\end{code}

(ℤ₀, ≡, ∼) is preorder

a) reflexive : if a ≡ b then a ∼ b
 
\begin{code}

refl'      :  _≡_ ⇒ _∼_
refl' refl = zrefl

_∼_isPreorder : IsPreorder _≡_ _∼_
_∼_isPreorder =  record
  { isEquivalence = PE.isEquivalence
  ; reflexive     = refl'
  ; trans         = _>∼<_
  }

_∼_preorder : Preorder _ _ _
_∼_preorder = record
  { Carrier    = ℤ₀
  ; _≈_        = _≡_
  ; _∼_        = _∼_
  ; isPreorder = _∼_isPreorder
  }
\end{code}

The properties about the sign functions

\begin{code}

sign◃ : ∀ n → sign n ◃ p n ∼ n
sign◃ (zero , zero)   = refl
sign◃ (zero , suc n)  = refl
sign◃ (suc m , zero)  = refl
sign◃ (suc m , suc n) = (sign◃ (m , n)) >∼< ⟨ sm+n≡m+sn m n ⟩

◃-cong-lem : ∀ {m n} → sign m ≡ sign n → p m 
  ≡ p n → sign m ◃ p m ≡ sign n ◃ p n
◃-cong-lem sign-≡ abs-≡ = cong₂ _◃_ sign-≡ abs-≡

◃-cong : ∀ {m n} → sign m ≡ sign n → p m ≡ p n → m ∼ n
◃-cong {m} {n} sign-≡ abs-≡ =
  (zsym (sign◃ m)) >∼< (refl' (◃-cong-lem {m} {n} sign-≡ abs-≡)) >∼< sign◃ n

\end{code}

ℕ*ℤ = i n * (x+ , x-) = n ℕ* x+ , n ℕ* x- 

\begin{code}

eqℕ*ℤ : ∀ n x → n ℕ*ℤ₀ x ∼ n ℕ*ℤ₀' x
eqℕ*ℤ n (x+ , x-) = (n ℕ* x+) +⋆ n+0≡n  >≡<
  ⟨ n+0≡n {n ℕ* x+} ⟩ ⋆+ (n ℕ* x-)

\end{code}

(ℤ₀ ,  ∼ , ≤ ) is decidable total order

a) ≤ to is decidable

\begin{code}

_≤?_ : Decidable _≤_
(x+ , x-) ≤? (y+ , y-) = (x+ ℕ+ y-) ℕ≤? (y+ ℕ+ x-)

\end{code}

b) (ℤ₀, ∼, ≤) is preorder

\begin{code}


ref≤ : {i j : ℤ₀} → i ∼ j → i ≤ j
ref≤ {y , y'} {y0 , y1} = refl′


≤isPreorder : IsPreorder _∼_ _≤_
≤isPreorder =  record
  { isEquivalence = _∼_isEquivalence
  ; reflexive     = ref≤
  ; trans         = trans′
  }
  where

\end{code}

transitivity:
a ≤ b → b ≤ c → a ≤ c

\begin{code}

  trans′ : Transitive _≤_
  trans′ {a , b} {c , d} {e , f} a+d≤c+b c+f≤e+d =
    ℕ+.+l-cancel′ (c ℕ+ d) $
    r-≤resp (exchange₂ a d c f) $
    l-≤resp (exchange₁ c b e d) $
    a+d≤c+b +≤ c+f≤e+d

\end{code}


≤ Respects₂ ∼:
a = b → c ≤ a → c ≤ b
b = c → b ≤ a → c ≤ a

\begin{code}

  ≤resp : _≤_ Respects₂ _∼_
  ≤resp = (λ a∼b c≤a → trans′ c≤a (ref≤ a∼b)) ,
          (λ b∼c b≤a → trans′ (ref≤ (zsym b∼c)) b≤a)

\end{code}

The symbol of transitivity of ≤

\begin{code}

infixl 40 _>≤<_

_>≤<_ : Transitive _≤_
_>≤<_ = IsPreorder.trans ≤isPreorder 

\end{code}

(ℤ₀, ∼, ≤) is decidable total order

\begin{code}

decTotalOrder : DecTotalOrder _ _ _
decTotalOrder = record
  { Carrier         = ℤ₀
  ; _≈_             = _∼_
  ; _≤_             = _≤_
  ; isDecTotalOrder = record
      { isTotalOrder = record
          { isPartialOrder = record
              { isPreorder = ≤isPreorder
              ; antisym  = antisym
              }
          ; total = total
          }
      ; _≟_  = _≟_
      ; _≤?_ = _≤?_
      }
  }
  where

\end{code}

antisymmetric:
a ≤ b → b ≤ a → a = b

\begin{code}

  antisym : Antisymmetric _∼_ _≤_
  antisym {a , b} {c , d} = ℕO.antisym

\end{code}

total: ∀ a b, a ≤ b ∨ b ≤ a 

\begin{code}

  total : Total _≤_
  total (a , b) (c , d) = ℕO.total (a ℕ+ d) (c ℕ+ b)

\end{code}

+ preserves ≤
a ≤ b → c ≤ d → a + c ≤ b + d

\begin{code}

+-pres₂′ : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
+-pres₂′ {a1 , a2} {b1 , b2} {c1 , c2} {d1 , d2} a≤b c≤d = 
  r-≤resp (exchange₃ a1 b2 c1 d2) $ 
  l-≤resp (exchange₃ b1 a2 d1 c2) $
  a≤b +≤ c≤d

\end{code}

+ cancellation for ≤
a + b ≤ a + c → b ≤ c

\begin{code}

+l-cancel′ : ∀ a {b c} → a + b ≤ a + c → b ≤ c
+l-cancel′ (a1 , a2) {b1 , b2} {c1 , c2} = 
  ℕ+.+l-cancel′ (a1 ℕ+ a2) ∘
  r-≤resp (exchange₃ a1 b1 a2 c2) ∘
  l-≤resp (exchange₃ a1 c1 a2 b2)


\end{code}

integrity for ≤
namely cancellation for multiplication
a + b ≤ a + c → b ≤ c

\begin{code}

integrity′ : ∀ {a b} c → (suc c , 0) * a
  ≤ (suc c , 0) * b → a ≤ b
integrity′ {a1 , a2} {b1 , b2} c = 
  ℕ+.integrity′ c ∘ 
  r-≤resp (ℤ₀i-lem₁ a1 b2 c) ∘
  l-≤resp (ℤ₀i-lem₁ b1 a2 c)


normal-ok : ∀ a → [ a ] ∼ a
normal-ok (_ , 0) = refl
normal-ok (0 , suc n) = refl
normal-ok (suc a , suc a') = normal-ok (a , a') >∼< ⟨ sm+n≡m+sn a a' ⟩ 

nm-lem : ∀ n n' → suc (n ℕ+ 0) ≡ suc (n' ℕ+ 0) → n ≡ n'
nm-lem n n' eq = ⟨ n+0≡n ⟩ >≡< (cong pred eq >≡< n+0≡n)

normal-unique : ∀ a b → a ∼ b → [ a ] ≡ [ b ]
normal-unique (zero , a') (zero , .a') refl = refl
normal-unique (zero , a') (suc n , zero) ()
normal-unique (zero , a') (suc n , suc n') eq = normal-unique (zero , a') (n , n') (cong pred eq)
normal-unique (suc n , zero) (zero , b') ()
normal-unique (suc n , zero) (suc n' , zero) eq with nm-lem n n' eq
normal-unique (suc .n' , zero) (suc n' , zero) eq | refl = refl
normal-unique (suc n , zero) (suc n' , suc n0) eq = normal-unique (suc n , zero) (n' , n0) (sm+n≡m+sn n n0 >≡< cong pred eq)
normal-unique (suc n , suc n') b eq = normal-unique (n , n') b (⟨ sm+n≡m+sn n n' ⟩ >∼< eq)

\end{code}
