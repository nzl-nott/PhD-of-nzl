
\AgdaHide{
\begin{code}
import Level
open import Relation.Binary.PropositionalEquality as PE hiding (refl ; sym ; trans; isEquivalence; [_])

module CwF-quotient (ext : Extensionality Level.zero Level.zero) where

open import Data.Unit
open import Function
open import Data.Product
open import Data.Bool
open import CategoryofSetoid
open import CwF-setoid

\end{code}
}

Quotient types

\begin{code}
module Q (Γ : Con)(A : Ty Γ)

         (R : (γ : ∣ Γ ∣) → ∣ [ A ]fm γ ∣ → ∣ [ A ]fm γ ∣ → Set)

         .(Rrespt : ∀{γ γ' : ∣ Γ ∣}
                   (p : [ Γ ] γ ≈ γ')
                   (a b : ∣ [ A ]fm γ ∣) →
                   .(R γ a b) → 
                   R γ' ([ A ]subst p a) ([ A ]subst p b))

         .(Rrsp : ∀ {γ a b} → .([ [ A ]fm γ ] a ≈ b) → R γ a b)

         .(Rref : ∀ {γ a} → R γ a a)
         .(Rsym : (∀ {γ a b} → .(R γ a b) → R γ b a))
         .(Rtrn :  (∀ {γ a b c} → .(R γ a b)
                 →  .(R γ b c) → R γ a c))
         where

  ⟦Q⟧₀ : ∣ Γ ∣ → Setoid
  ⟦Q⟧₀ γ = record
         { Carrier = ∣ [ A ]fm γ ∣
         ; _≈_ = R γ
         ; refl = Rref
         ; sym = Rsym
         ; trans = Rtrn
         }


  ⟦Q⟧ : Ty Γ
  ⟦Q⟧ = record 
    { fm = ⟦Q⟧₀
    ; substT = [ A ]subst
    ; subst* = λ p q → Rrespt p _ _ q
    ; refl* = Rrsp [ A ]refl*
    ; trans* = λ a → Rrsp ([ A ]trans* _)
    }

  ⟦[_]⟧ : Tm A → Tm ⟦Q⟧
  ⟦[ x ]⟧ = record
           { tm = [ x ]tm
           ; respt = λ p → Rrsp ([ x ]respt p)
           }
  
  ⟦[_]⟧' : Tm (A ⇒ ⟦Q⟧)
  ⟦[_]⟧' = record
           { tm = λ x → (λ a → a) , 
                  (λ a b p → 
                  Rrsp ([ [ A ]fm _ ]trans [ A ]refl* p))
           ; respt = λ p a → Rrsp [ A ]tr*
           }
\end{code}

\begin{code}  
  .Q-Ax : ∀ γ a b → [ [ A ]fm γ ] a ≈ b → [ [ ⟦Q⟧ ]fm _ ] a ≈ b
  Q-Ax γ a b = Rrsp

  Q-elim : (B : Ty Γ)(f : Tm (A ⇒ B))
           (frespR : ∀ γ a b → (R γ a b)
                  → [ [ B ]fm γ ] prj₁ ([ f ]tm γ) a 
                    ≈  prj₁ ([ f ]tm γ) b)
         → Tm (⟦Q⟧ ⇒ B)
  Q-elim B f frespR = record
           { tm = λ γ → prj₁ ([ f ]tm γ) , (λ a b p → 
                  [ [ B ]fm _ ]trans [ B ]refl* (frespR _ _ _ p))
           ; respt = λ {γ} {γ'} p a → [ f ]respt p a
           }

  
  substQ : (Γ & A) ⇉ (Γ & ⟦Q⟧)
  substQ = record
           { fn = λ {(x , a) → x , a}
           ; resp = λ{ (p , q) → p , (Rrsp q)}
           }

  Q-ind : (P : Ty (Γ & ⟦Q⟧))
         → (isProp : ∀ {x a} (r s : ∣ [ P ]fm (x , a) ∣) → 
                      [ [ P ]fm (x , a) ] r ≈ s )
         → (h : Tm (Π A (P [ substQ ]T)))
         → Tm (Π ⟦Q⟧ P)
  Q-ind P isProp h = record
           { tm = λ x → (prj₁ ([ h ]tm x)) , 
                  (λ a b p → isProp {x} {b} _ _)
           ; respt = [ h ]respt
           }
\end{code}