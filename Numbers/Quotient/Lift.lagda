
Lift operators for definable quotients

\begin{code}

open import Quotient
open import Data.Nat
open import Relation.Binary.PropositionalEquality as PE hiding (cong)

module Quotient.Lift
         {S : Setoid}{PQ : PreQu S}(QUD : QuD PQ) where


open QuD QUD renaming (emb to ⌜_⌝)
open Setoid S renaming (Carrier to Q₀ ; _≈_ to _∼_)
open PreQu PQ

private
  Op : ℕ → (A : Set) → Set
  Op 0 A = A
  Op (ℕ.suc n) A = A → Op n A

-- unsafe lift functions for operators

  liftOp : (n : ℕ) → Op n Q₀ → Op n Q
  liftOp 0 op = [ op ]
  liftOp (ℕ.suc n) op = λ x → liftOp n (op ⌜ x ⌝)


  Cong1 : Op 1 Q₀ → Set
  Cong1 f = ∀ {a b} → a ∼ b → f a ∼ f b

  Cong2 : Op 2 Q₀ → Set
  Cong2 op = ∀ {a b c d} → a ∼ b → c ∼ d → op a c ∼ op b d

record Op1 : Set where
  constructor _,_
  field
    op : Op 1 Q₀
    cong : Cong1 op


record Op2 : Set where
  constructor _,_
  field
    op : Op 2 Q₀
    cong : Cong2 op


liftOp1 : (f : Op1) → Op 1 Q
liftOp1 (f , cong) = λ n → [ f ⌜ n ⌝ ]

liftOp2 : (op : Op2) → Op 2 Q
liftOp2 ( _op_ , cong) = λ m n → [ ⌜ m ⌝ op ⌜ n ⌝ ]

private
  compl : ∀ {n} → ⌜ [ n ] ⌝ ∼ n
  compl {n} = complete n

  ⌞_⌟          : ∀ {i j} → ⌜ i ⌝ ∼ ⌜ j ⌝  → i ≡ j
  ⌞_⌟ {i} {j} eq = PE.trans (PE.trans (PE.sym (stable i)) (sound eq)) (stable j)

  sound' : ∀ {i j} → i ∼ ⌜ j ⌝  → [ i ] ≡ j
  sound' {i} {j} eq = PE.trans (sound eq) (stable j)


liftOp1-β : (f : Op1) → ∀ n → liftOp1 f [ n ] ≡ [ Op1.op f n ] 
liftOp1-β (f , cong) n = sound (cong compl)

liftOp2-β : (op : Op2) → ∀ m n → liftOp2 op [ m ] [ n ] ≡ [ Op2.op op m n ] 
liftOp2-β (op , cong) m n = sound (cong compl compl)

lift21 : (op : Op2) → ∀ a b c → Op2.op op ⌜ a ⌝ ⌜ b ⌝ ∼ ⌜ c ⌝ → liftOp2 op a b ≡ c
lift21 (op , cong) a b c = sound'


lift21' : {op : Op 2 Q₀} → ∀ a b c → op ⌜ a ⌝ ⌜ b ⌝ ∼ ⌜ c ⌝ → liftOp 2 op a b ≡ c
lift21' a b c = sound'

\end{code}