\AgdaHide{
\begin{code}

module CwF-setoid where

open import CategoryofSetoid
open import Data.Product
open import Function
open import Data.Nat
open import Data.Empty
open import Data.Unit

\end{code}
}

\section{Categories with families}

Context are interpreted as setoids

\begin{code}
Con = Setoid
\end{code}

Semantic Types

\begin{code}
record Ty (Γ : Setoid) : Set₁ where
  field
    fm     : ∣ Γ ∣ → Setoid
    substT : {x y : ∣ Γ ∣} → 
             .([ Γ ] x ≈ y) →
             ∣ fm x ∣ → 
             ∣ fm y ∣
    .subst* : ∀{x y : ∣ Γ ∣}
             (p : ([ Γ ] x ≈ y))
             {a b : ∣ fm x ∣} →
             .([ fm x ] a ≈ b) →
             ([ fm y ] substT p a ≈ substT p b)

    .refl*  : ∀{x : ∣ Γ ∣}{a : ∣ fm x ∣} → 
             [ fm x ] substT ([ Γ ]refl) a ≈ a
    .trans* : ∀{x y z : ∣ Γ ∣}
             {p : [ Γ ] x ≈ y}
             {q : [ Γ ] y ≈ z}
             (a : ∣ fm x ∣) → 
             [ fm z ] substT q (substT p a) 
            ≈ substT ([ Γ ]trans p q) a

  .tr* : ∀{x y : ∣ Γ ∣}
          {p : [ Γ ] y ≈ x}
          {q : [ Γ ] x ≈ y}
          {a : ∣ fm x ∣} → 
          [ fm x ] substT p (substT q a) ≈ a
  tr* = [ fm _ ]trans (trans* _) refl*

  substT-inv : {x y : ∣ Γ ∣} → 
             .([ Γ ] x ≈ y) →
             ∣ fm y ∣ → 
             ∣ fm x ∣
  substT-inv p y = substT ([ Γ ]sym p) y
\end{code}

\AgdaHide{
\begin{code}
  subst-mir1 : ∀{x y : ∣ Γ ∣}{P : Set}
              {p : [ Γ ] x ≈ y}{q : [ Γ ] y ≈ x}
              {a : ∣ fm x ∣}{b : ∣ fm y ∣} → 
              (.([ fm y ] substT p a ≈ b) → P) 
             → (.([ fm x ] a ≈ substT q b) → P)
  subst-mir1 eq p = eq ([ fm _ ]trans (subst* _ p) tr*)

open Ty public 
  renaming (substT to [_]subst; substT-inv to [_]subst-inv
           ; subst* to [_]subst*; fm to [_]fm ;
            refl* to [_]refl* ; trans* to [_]trans*; tr* to [_]tr*)

\end{code}
}

\begin{code}
_[_]T : ∀ {Γ Δ : Setoid} → Ty Δ → Γ ⇉ Δ → Ty Γ
_[_]T {Γ} {Δ} A f
     = record
     { fm     = λ x → fm (fn x)
     ; substT = λ p → substT _
     ; subst* = λ p → subst* (resp p)
     ; refl*  = refl*
     ; trans* = trans*
     }
     where 
       open Ty A
       open _⇉_ f
\end{code}


Semantic Terms

\begin{code}
record Tm {Γ : Con}(A : Ty Γ) : Set where
  constructor tm:_resp:_
  field
    tm    : (x : ∣ Γ ∣) → ∣ [ A ]fm x ∣
    .respt : ∀ {x y : ∣ Γ ∣} → 
          (p : [ Γ ] x ≈ y) → 
          [ [ A ]fm y ] [ A ]subst p (tm x) ≈ tm y
open Tm public renaming (tm to [_]tm ; respt to [_]respt)
\end{code}

Term substitution

\begin{code}
_[_]m : ∀ {Γ Δ : Con}{A : Ty Δ} → Tm A 
      → (f : Γ ⇉ Δ) → Tm (A [ f ]T)
_[_]m t f = record 
          { tm = [ t ]tm ∘ [ f ]fn
          ; respt = [ t ]respt ∘ [ f ]resp 
          }
\end{code}

Context comprehension

\begin{code}
_&_ : (Γ : Setoid) → Ty Γ → Setoid
Γ & A = 
  record { Carrier = Σ[ x ∶ ∣ Γ ∣ ] ∣ fm x ∣ 
         ; _≈_ = λ{(x , a) (y , b) → 
             Σ[ p ∶ x ≈ y ] [ fm y ] (substT p a) ≈ b }
         ; refl = refl , refl*
         ; sym =  λ {(p , q) → (sym p) , 
             [ fm _ ]trans (subst* _ ([ fm _ ]sym q)) tr* }
         ; trans = λ {(p , q) (m , n) → trans p m ,
                   [ fm _ ]trans ([ fm _ ]trans 
                   ([ fm _ ]sym (trans* _)) (subst* _ q)) n}
         }
    where
      open Setoid Γ
      open Ty A


infixl 5 _&_

fst& : {Γ : Con}{A : Ty Γ} → Γ & A ⇉ Γ
fst& = record 
         { fn = proj₁
         ; resp = proj₁
         }
\end{code}

Pairing operation

\begin{code}
_,,_ : {Γ Δ : Con}{A : Ty Δ}(f : Γ ⇉ Δ) 
     → (Tm (A [ f ]T)) → Γ ⇉ (Δ & A)
f ,, t = record 
         { fn = < [ f ]fn , [ t ]tm >
         ; resp = < [ f ]resp , [ t ]respt >
         }
\end{code}

Projections

\begin{code}
fst : {Γ Δ : Con}{A : Ty Δ} → Γ ⇉ (Δ & A) → Γ ⇉ Δ
fst f = record 
        { fn = proj₁ ∘ [ f ]fn
        ; resp = proj₁ ∘ [ f ]resp 
        }

snd : {Γ Δ : Con}{A : Ty Δ} → (f : Γ ⇉ (Δ & A))
    → Tm (A [ fst {A = A} f ]T)
snd f = record 
        { tm = proj₂ ∘ [ f ]fn
        ; respt = proj₂ ∘ [ f ]resp 
        }

_^_ : {Γ Δ : Con}(f : Γ ⇉ Δ)(A : Ty Δ) 
    → Γ & A [ f ]T ⇉ Δ & A
f ^ A = record 
        { fn = < [ f ]fn ∘ proj₁ , proj₂ >
        ; resp = < [ f ]resp ∘ proj₁ , proj₂ >
        }
\end{code}

$\Pi$-types (object level)

\begin{code}
Π : {Γ : Setoid}(A : Ty Γ)(B : Ty (Γ & A)) → Ty Γ
Π {Γ} A B = record 
  { fm = λ x → let Ax = [ A ]fm x in
               let Bx = λ a → [ B ]fm (x , a) in
         record
         { Carrier = Subset ((a : ∣ Ax ∣) → ∣ Bx a ∣) (λ fn → 
                     (a b : ∣ Ax ∣)
                     (p : [ Ax ] a ≈ b) →
                     [ Bx b ] [ B ]subst ([ Γ ]refl , 
                     [ Ax ]trans [ A ]refl* p) (fn a) ≈ fn b)


         ; _≈_    = λ{(f , _) (g , _) → ∀ a → [ Bx a ] f a ≈ g a }
         ; refl    = λ a → [ Bx _ ]refl 
         ; sym     = λ f a → [ Bx _ ]sym (f a)
         ; trans   = λ f g a → [ Bx _ ]trans (f a) (g a)
         }

  ; substT = λ {x} {y} p → λ {(f , rsp) →
                   let y2x = λ a → [ A ]subst ([ Γ ]sym p) a in
                   let x2y = λ a → [ A ]subst p a in
             (λ a → [ B ]subst (p , [ A ]tr*) 
             (f (y2x a))) , 
             (λ a b q →
                let a' = y2x a in 
                let b' = y2x b in
                let q' = [ A ]subst* ([ Γ ]sym p) q in
                let H = rsp a' b' ([ A ]subst* ([ Γ ]sym p) q) in
                let r : [ Γ & A ] (x , b') ≈ (y , b)
                    r = (p , [ A ]tr*) in
                let pre = [ B ]subst* r 
                        (rsp a' b' ([ A ]subst* ([ Γ ]sym p) q)) in 
                [ [ B ]fm (y , b) ]trans 
                ([ B ]trans* _) 
                ([ [ B ]fm (y , b) ]trans 
                ([ [ B ]fm (y , b) ]sym ([ B ]trans* _)) 
                pre))}


  ; subst* = λ _ q _ → [ B ]subst* _ (q _)
  ; refl* = λ {x} {a} ax 
          → let rsp = prj₂ a in (rsp _ _ [ A ]refl*)
  ; trans* =  λ {(f , rsp) a →
             [ [ B ]fm _ ]trans 
             ([ [ B ]fm _ ]trans 
             ([ B ]trans* _) 
             ([ [ B ]fm _ ]sym ([ B ]trans* _)))
             ([ B ]subst* _ (rsp _ _ ([ A ]trans* _) )) }
  }


lam : {Γ : Con}{A : Ty Γ}{B : Ty (Γ & A)} → Tm B → Tm (Π A B)
lam {Γ} {A} (tm: tm resp: respt) = 
  record { tm = λ x → (λ a → tm (x , a)) 
                , (λ a b p → respt ([ Γ ]refl , 
                [ [ A ]fm x ]trans [ A ]refl* p))
         ; respt = λ p _ → respt (p , [ A ]tr*)
         }


app : {Γ : Con}{A : Ty Γ}{B : Ty (Γ & A)} → Tm (Π A B) → Tm B
app {Γ} {A} {B} (tm: tm resp: respt) = 
  record { tm = λ {(x , a) → prj₁ (tm x) a}
         ; respt = λ {x} {y} → λ {(p , tr) → 
                 let fresp = prj₂ (tm (proj₁ x)) in
                 [ [ B ]fm _ ]trans 
                 ([ B ]subst* (p , tr) 
                 ([ [ B ]fm _ ]sym [ B ]refl*))
                 ([ [ B ]fm _ ]trans
                 ([ B ]trans* {p = ([ Γ ]refl , [ A ]refl*)} _)
        
                 ([ [ B ]fm _ ]trans 
                 ([ [ B ]fm _ ]sym 
                 ([ B ]trans* {q = (p , [ A ]tr*)} _))
                 ([ [ B ]fm _ ]trans 
                 ([ B ]subst* _ (fresp _ _ 
                   ([ [ A ]fm _ ]trans ([ [ A ]fm _ ]sym [ A ]tr*) 
                   ([ A ]subst* ([ Γ ]sym p) tr))))
                 (respt p _)))) }
         }

_⇒_ : {Γ : Con}(A B : Ty Γ) → Ty Γ
A ⇒ B = Π A (B [ fst& {A = A} ]T)

infixr 6 _⇒_
\end{code}

Simpler definition for functions

\begin{code}
[_,_]_⇒fm_ : (Γ : Con)(x : ∣ Γ ∣) 
           → Setoid → Setoid → Setoid
[ Γ , x ] Ax ⇒fm Bx 
  = record
      { Carrier = Σ[ fn ∶ (∣ Ax ∣ → ∣ Bx ∣) ] ((a b : ∣ Ax ∣)
                  (p : [ Ax ] a ≈ b) → [ Bx ] fn a ≈ fn b)
      ; _≈_    = λ{(f , _) (g , _) → ∀ a → [ Bx ] f a ≈ g a }
      ; refl    = λ _ → [ Bx ]refl 
      ; sym     = λ f a → [ Bx ]sym (f a)
      ; trans   = λ f g a → [ Bx ]trans (f a) (g a)
      }
\end{code}

$\Sigma$-types (object level)

\begin{code}

Σ' : {Γ : Con}(A : Ty Γ)(B : Ty (Γ & A)) → Ty Γ
Σ' {Γ} A B = record 
        { fm = λ x → let Ax = [ A ]fm x in
               let Bx = λ a → [ B ]fm (x , a) in
         record
           { Carrier = Σ[ a ∶ ∣ Ax ∣ ] ∣ Bx a ∣

           ; _≈_    = λ{(a₁ , b₁) (a₂ , b₂) → 
                      Subset ([ Ax ] a₁ ≈ a₂) 
                      (λ eq₁ → [ Bx _ ] [ B ]subst 
                       ([ Γ ]refl , [ [ A ]fm x ]trans 
                       [ A ]refl* eq₁) b₁ ≈ b₂)
           }

           ; refl    = λ {t} → [ Ax ]refl , [ B ]refl*

           ; sym     = λ {(p , q) → ([ Ax ]sym p) , 
                       [ Bx _ ]trans ([ B ]subst* _ 
                       ([ Bx _ ]sym q)) [ B ]tr*}

           ; trans   = λ {(p , q) (r , s) → ([ Ax ]trans p r) ,
                       [ Bx _ ]trans ([ Bx _ ]trans 
                       ([ Bx _ ]sym ([ B ]trans* _)) 
                       ([ B ]subst* _ q)) s}
           }

        ; substT = λ x≈y → λ {(p , q) → 
                   ([ A ]subst x≈y p) , [ B ]subst (x≈y , 
                   [ [ A ]fm _ ]refl) q}

        ; subst* = λ x≈y → λ {(p , q) → [ A ]subst* x≈y p , 
                   [ [ B ]fm _ ]trans ([ [ B ]fm _ ]trans 
                   ([ B ]trans* _)
                   ([ [ B ]fm _ ]sym ([ B ]trans* _))) 
                   ([ B ]subst* (x≈y , [ [ A ]fm _ ]refl) q) }
        ; refl* = λ {x} {a} → 
                  let (p , q) = a in [ A ]refl* , [ B ]tr*
        ; trans* =  λ {(p , q)  → ([ A ]trans* _) , 
                    ([ [ B ]fm _ ]trans
                    ([ B ]trans* _) ([ B ]trans* _)) }
        }

\end{code}

Binary relation

\begin{code}
Rel : {Γ : Con} → Ty Γ → Set₁
Rel {Γ} A = Ty (Γ & A & A [ fst& {A = A} ]T)
\end{code}

Natural numbers

Axiom: irrelevant:

\begin{code}
postulate
    .irrelevant : {A : Set} → .A → A
\end{code}


\begin{code}
module Natural (Γ : Con) where

  _≈nat_ : ℕ → ℕ → Set
  zero ≈nat zero = ⊤
  zero ≈nat suc n = ⊥
  suc m ≈nat zero = ⊥
  suc m ≈nat suc n = m ≈nat n
  
  reflNat : {x : ℕ} → x ≈nat x
  reflNat {zero} = tt
  reflNat {suc n} = reflNat {n}

  symNat : {x y : ℕ} → x ≈nat y → y ≈nat x
  symNat {zero} {zero} eq = tt
  symNat {zero} {suc _} eq = eq
  symNat {suc _} {zero} eq = eq
  symNat {suc x} {suc y} eq = symNat {x} {y} eq

  transNat : {x y z : ℕ}
           → x ≈nat y → y ≈nat z → x ≈nat z
  transNat {zero} {zero} xy yz = yz
  transNat {zero} {suc _} () yz
  transNat {suc _} {zero} () yz
  transNat {suc _} {suc _} {zero} xy yz = yz
  transNat {suc x} {suc y} {suc z} xy yz =
           transNat {x} {y} {z} xy yz
   

  ⟦Nat⟧ : Ty Γ
  ⟦Nat⟧ = record 
    { fm = λ γ → record
         { Carrier = ℕ
         ; _≈_ = _≈nat_
         ; refl = λ {n} → reflNat {n}
         ; sym = λ {x} {y} → symNat {x} {y}
         ; trans = λ {x} {y} {z} → transNat {x} {y} {z}
         }
    ; substT = λ _ n → n
    ; subst* = λ _ x → irrelevant x
    ; refl* = λ {x} {a} → reflNat {a}
    ; trans* = λ a → reflNat {a} 
    }

  ⟦0⟧ : Tm ⟦Nat⟧
  ⟦0⟧ = record
      { tm = λ _ → 0
      ; respt = λ p → tt
      }

  ⟦s⟧ : Tm ⟦Nat⟧ → Tm ⟦Nat⟧
  ⟦s⟧ (tm: t resp: respt) 
      = record
      { tm = suc ∘ t
      ; respt = respt
      }
\end{code}

Simply typed universe

\AgdaHide{
\begin{code}
  data ⟦U⟧⁰ : Set where
    nat : ⟦U⟧⁰
    arr<_,_> : (a b : ⟦U⟧⁰) → ⟦U⟧⁰

  _~⟦U⟧_ : ⟦U⟧⁰ → ⟦U⟧⁰ → Set -- HProp
  nat ~⟦U⟧ nat = ⊤
  nat ~⟦U⟧ arr< a , b > = ⊥
  arr< a , b > ~⟦U⟧ nat = ⊥
  arr< a , b > ~⟦U⟧ arr< a' , b' > = a ~⟦U⟧ a' × b ~⟦U⟧ b'

  reflU :  {x : ⟦U⟧⁰} → x ~⟦U⟧ x
  reflU {nat} = tt
  reflU {arr< a , b >} = reflU {a} , reflU {b}

  symU : {x y : ⟦U⟧⁰} → x ~⟦U⟧ y → y ~⟦U⟧ x
  symU {nat} {nat} eq = tt
  symU {nat} {arr< a , b >} eq = eq
  symU {arr< a , b >} {nat} eq = eq
  symU {arr< a , b >} {arr< a' , b' >} (p , q) = (symU {a} {a'} p) 
                                               , (symU {b} {b'} q)

  transU : {x y z : ⟦U⟧⁰} → x ~⟦U⟧ y → y ~⟦U⟧ z → x ~⟦U⟧ z
  transU {nat} {nat} eq1 eq2 = eq2
  transU {nat} {arr< a , b >} () eq2
  transU {arr< a , b >} {nat} () eq2
  transU {arr< a , b >} {arr< a' , b' >} {nat} eq1 eq2 = eq2
  transU {arr< a , b >} {arr< a' , b' >} {arr< a0 , b0 >} (p1 , q1) 
         (p2 , q2) = (transU {a} {a'} {a0} p1 p2) 
         , transU {b} {b'} {b0} q1 q2

  ⟦U⟧ : Ty Γ
  ⟦U⟧ = record 
    { fm = λ γ → record
         { Carrier = ⟦U⟧⁰
         ; _≈_ = _~⟦U⟧_
         ; refl = λ {x} → reflU {x}
         ; sym = λ {x} {y} → symU {x} {y}
         ; trans = λ {x} {y} {z} → transU {x} {y} {z}
         }
    ; substT = λ _ x → x
    ; subst* =  λ _ x → irrelevant x
    ; refl* = λ {x} {a} → reflU {a}
    ; trans* = λ a → reflU {a}
    }

  elfm : Σ ∣ Γ ∣ (λ x → ⟦U⟧⁰) → Setoid
  elfm (γ , nat) = [ ⟦Nat⟧ ]fm γ
  elfm (γ , arr< a , b >) = [ Γ , γ ] elfm (γ , a) ⇒fm elfm (γ , b)
\end{code}
}