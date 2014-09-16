{-# OPTIONS --type-in-type #-}

\begin{code}
import Level
open import Relation.Binary.PropositionalEquality as PE hiding (refl ; sym ; trans; isEquivalence; [_])

module Cwf-quotient (ext : Extensionality Level.zero Level.zero) where


import CwF-setoid


open CwF-setoid ext

module Quotient-type (Γ : Con)(A : Ty Γ)(eqv : Rel A)  where
  ⟦Qt⟧ : Ty (Γ & A & A [ fst& {A = A} ]T & eqv)
  ⟦Qt⟧ = record 
       { fm = λ {x → {!x!} }
       ; substT = {!!}; subst* = {!!}; refl* = {!!}; trans* = {!!} }

\end{code}