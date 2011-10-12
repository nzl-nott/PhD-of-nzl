\begin{code}

{-# OPTIONS --universe-polymorphism #-}

module Data.Real where

open import Data.Bool
open import Data.Empty
import Data.Nat as ℕ -- using (ℕ ; fold ; pred ; s≤s ; z≤n) 
open import Level
open import Data.Product
import Data.Integer.Setoid as ℤ₀
open import Data.Integer' using (ℤ ; +_)
import Data.Rational' as ℚ₀ -- using (ℚ₀ ; _/suc_ ; _∼_ ; abscanc ; is+ ; ∣_∣) renaming (_+_ to _ℚ₀+_; _-_ to _ℚ₀-_; _≤_ to _ℚ₀≤_ ; _<_ to _ℚ₀<_)

open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Algebra.FunctionProperties.Core


private
 module Definition where

   open ℚ₀ hiding (_+_ ; ∣_∣ ; _<_) renaming (∣_∣₂ to ∣_∣)
   open ℕ
 
   _>0 = is+

   Seq : (A : Set) → Set
   Seq A = ℕ → A


   Converge : Seq ℚ₀ → Set
   Converge f = ∀ (ε : ℚ₀*) → ∃ λ lb → ∀ m n → ∣ (f (suc lb + m)) - (f (suc lb + n)) ∣ <' ε

{- old version
   Converge : Seq ℚ₀ → Set
   Converge f = ∀ (ε : ℚ₀*) → ∃ λ lb → ∀ m n → (lb < m) → (lb < n) →  ∣ (f m) - (f n) ∣ <' ε
-}
   record ℝ₀ : Set where
     constructor f:_p:_
     field
       f : Seq ℚ₀
       p : Converge f


   _Diff_on_ : Seq ℚ₀ → Seq ℚ₀ → Seq ℚ₀*
   f Diff g on m = ∣ f m - g m ∣

   _~_ : Rel ℝ₀ zero
   (f: f p: p) ~ (f: f' p: p') =  
       ∀ (ε : ℚ₀*) → ∃ λ lb → ∀ i → (lb < i) → f Diff f' on i <' ε

open Definition public


open ℕ using (suc) renaming (_≤_ to _ℕ≤_)
open ℚ₀ using (ℚ₀) renaming (_/2' to _/2 ; ∣_∣₂ to ∣_∣)

liftSQ : Op₂ ℚ₀ → Op₂ (Seq ℚ₀)
liftSQ _*_ = λ sq1 sq2 m → sq1 m * sq2 m

retrPrf1 : ∀ m n → ℤ₀.ℕGE m n ≡ true → n ℕ≤ m
retrPrf1  m 0 rt = ℕ.z≤n
retrPrf1 0 (suc n) ()
retrPrf1 (suc n) (suc n') rt = ℕ.s≤s (retrPrf1 n n' rt)


retrPrf2 : ∀ m n → ℤ₀.ℕGE m n ≡ false → m ℕ≤ n
retrPrf2 0 n rt = ℕ.z≤n
retrPrf2 (suc n) 0 ()
retrPrf2 (suc n) (suc n') rt = ℕ.s≤s (retrPrf2 n n' rt)

private
  module prf+ where
    open ℚ₀ hiding (∣_∣) renaming (∣_∣₂ to ∣_∣)
    open import Data.Rational.Properties

    lem1 : ∀ a b c d → ∣ (a + b) - (c + d) ∣ ≡ ∣ (a - c) + (b - d) ∣
    lem1 a b c d = cong ∣_∣ {!!}

prf+ : ∀ a b → Converge (liftSQ ℚ₀._+_ (ℝ₀.f a) (ℝ₀.f b))
prf+ (f: f p: p) (f: f' p: p') ep with (p (ep /2)) | (p' (ep /2))
... | lb1 , y1 | lb2 , y2 with inspect (ℤ₀.ℕGE lb1 lb2)
... | true with-≡ eq = lb1 , λ m n → {!!}

-- | (f m + f' m) - (f n + f' n) | = | (f m - f n) + (f' m - f' n) | ≤ | (f m - f n) | + | (f' m - f' n) | ≤ ep /2 + ep/2

... | false with-≡ eq = lb2 , {!!}


_+_ : Op₂ ℝ₀
a + b = f: liftSQ ℚ₀._+_ (ℝ₀.f a) (ℝ₀.f b) p: prf+ a b


prf* : ∀ a b → Converge (liftSQ ℚ₀._*_ (ℝ₀.f a) (ℝ₀.f b))
prf* = {!!}


_*_ : Op₂ ℝ₀
a * b = f: liftSQ ℚ₀._*_ (ℝ₀.f a) (ℝ₀.f b) p: prf* a b

\end{code}





{-
abs-out : ∀ a b a' b' → ℚ₀∣ (a ℚ₀+ a') ℚ₀- (b ℚ₀+ b') ∣  ℚ₀≤ ℚ₀∣ a ℚ₀- b ∣  ℚ₀+ ℚ₀∣ a' ℚ₀- b' ∣ 
abs-out ab a' b' = {!!}


add-pre : ∀ {a b c d} → a ℚ₀< b → c ℚ₀< d → a ℚ₀+ c ℚ₀< b ℚ₀+ d
add-pre = {!!}


trans' : ∀ {a b c d} → a ℚ₀≤ d → b ℚ₀< c → a ℚ₀< c
trans' = {!!}

changeR : ∀ {a b c d} → (b ℚ₀+ c) ∼ d → a ℚ₀< b ℚ₀+ c → a ℚ₀< d
changeR = {!!}
 
-}