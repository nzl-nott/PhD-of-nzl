\AgdaHide{

\begin{code}
module Span where

open import AIOOG
open import AIOOGS2
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

Span' : ℕ → Σ Con Ty
Span' zero = ε , *
Span' (suc n) = let (Γ , A) = Span' n in
                   (Γ , A , A +T A) , (var (vS v0) =h var v0)

Stalk : ℕ → Con
Stalk n = proj₁ (Span' n)

Peak : (n : ℕ) → Ty (Stalk n)
Peak n = proj₂ (Span' n)

Span : ℕ → Con
Span n = Stalk n , Peak n

SpanisContr : (n : ℕ) → isContr (Span n)
SpanisContr 0 = c*
SpanisContr (suc n) = ext (SpanisContr n) v0

src : (n : ℕ) → Span (suc n) ⇒ Span n
src n = IdCm +S _ +S _

tgt : (n : ℕ) → Span (suc n) ⇒ Span n
tgt n = (IdCm +S _ +S _ +S _) , (var (vS v0) ⟦ wk+S+T (wk+S+T (wk+S+T IC-T)) ⟫)

inj-stalk : (n : ℕ) →  Span n ⇒ Stalk (suc n)
inj-stalk n = IdCm , (var v0 ⟦ IC-T ⟫)

inj-l1 : (n : ℕ) → Peak (suc n) [ inj-stalk n ]T ≡ (var v0 =h var v0)
inj-l1 n = trans wk-hom (hom≡ (wk-coh ∾ cohOp (trans [+S]T (wk-T IC-T))) (cohOp IC-T))

inj : (n : ℕ) →  Span n ⇒ Span (suc n)
inj n = (inj-stalk n) , JJ (SpanisContr n) IdCm (var v0 =h var v0) ⟦ trans (inj-l1 n) (sym IC-T) ⟫


src-itr : (k n : ℕ) → Span (k + n) ⇒ Span n
src-itr zero n = IdCm
src-itr (suc k) n = src-itr k n ⊚ src (k + n)


tgt-itr : (k n : ℕ) → Span (k + n) ⇒ Span n
tgt-itr zero n = IdCm
tgt-itr (suc k) n = tgt-itr k n ⊚ tgt (k + n)

\end{code}
}