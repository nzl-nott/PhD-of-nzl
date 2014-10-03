\begin{code}


module COS2 where

open import Relation.Binary

open Setoid remaing (Carrier to ∣_∣)
Con = Setoid

{-
record Ty (Γ : Con) : Set₁ where
  field
    fm     : ∣ Γ ∣ → Setoid -- the setoid of types associated to Context Γ

-- substT p is the homomorphism between setoid of types, substitution of terms

    substT : {x y : ∣ Γ ∣} → 
             [ Γ ] x ≈ y →
             ∣ fm x ∣ → 
             ∣ fm y ∣
    subst* : ∀{x y : ∣ Γ ∣}  -- substT respects the equality
             (p : [ Γ ] x ≈ y)
             {a b : ∣ fm x ∣} →
             [ fm x ] a ≈ b →
             [ fm y ] substT p a ≈ substT p b

-- beta equality (Computation rules)

    refl*  : ∀(x : ∣ Γ ∣)
             (a : ∣ fm x ∣) → 
             [ fm x ] substT [ Γ ]refl a ≈ a
    trans* : ∀{x y z : ∣ Γ ∣}
             {p : [ Γ ] x ≈ y}
             {q : [ Γ ] y ≈ z}
             (a : ∣ fm x ∣) → 
             [ fm z ] substT q (substT p a) ≈ substT ([ Γ ]trans p q) a


-}


\end{code}