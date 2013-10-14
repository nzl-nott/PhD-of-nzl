\documentclass[a4paper,12pt]{article}

\usepackage[utf8x]{inputenc}
\usepackage{ucs}
\usepackage{cite}
\usepackage{MnSymbol}

\begin{document}

\section{Appendix}

\begin{code}

module Quotient-new where

open import Data.Product
open import Function
import Level
open import Relation.Binary.Core
import Relation.Binary as RB

open RB.Setoid renaming 
  (Carrier to ∣_∣; refl to refl-s; sym to sym-s; trans to trans-s)

Setoid = RB.Setoid Level.zero Level.zero

open import Relation.Binary.PropositionalEquality as PE
  hiding (isEquivalence ; [_])

open import ThomasProperties


-- setoid morphism

record _→s_ (A B : Setoid) : Set where
  private
    _≈A_ = _≈_ A
    _≈B_ = _≈_ B
  field
    fun : ∣ A ∣ → ∣ B ∣
    fun-correct : ∀ {a b} → a ≈A b → fun a ≈B fun b -- functorial



record depSetoid (A : Setoid) : Set₁ where
  field
    obj : ∣ A ∣ → Setoid
    coh :  ∀ {a b} → _≈_ A a b → ∣ obj a ∣ → ∣ obj b ∣

record _→s-dep_ (A : Setoid)(B : depSetoid A) : Set where
  private
    _≈A_ = _≈_ A
  open depSetoid B
  field
    fun-d : (a : ∣ A ∣) → ∣ obj a ∣ 
    fun-d-correct : ∀ {a b} → (p : a ≈A b) →  _≈_ (obj b) (coh p (fun-d a)) (fun-d b)

\end{code}

\emph{Prequotients}

Cone

\begin{code}

∇ : Set → Setoid
∇ A = record { Carrier = A
             ; _≈_ = _≡_
             ; isEquivalence = PE.isEquivalence }

record pre-Quotient (A : Setoid) : Set₁ where
  field
    Q  : Set
    nf : A →s ∇ Q


\end{code}

\emph{Quotients as prequotients with a dependent eliminator.}
colimit

\begin{code}

record Quotient {A : Setoid} (PQ : pre-Quotient A) : Set₁ where
  open pre-Quotient PQ
  open _→s_ nf renaming (fun to [_]; fun-correct to sound)
  field

    qelim : {B : Q → Set}
          → (f : A  →s-dep (record { obj = λ a → ∇ (B [ a ]); coh = λ p → subst B (sound p) }))
          →  (q : Q) → B q

{-
    qelim   : {B : Q → Set}
            → (f : (a : ∣ A ∣) → B [ a ])
            → ((a b : ∣ A ∣) → (p : _≈_ A a b) 
                → subst B (sound p) (f a) ≡ f b)
            → (q : Q) → B q
    qelim-β : ∀ {B a f} q → qelim {B} f q [ a ]  ≡ f a
-}
open Quotient


-- A →s Q

-- Q →s B
\end{code}

\emph{Proof irrelevance of qelim}
\begin{code}

{-
qelimIrr : {S : Setoid}{PQ : pre-Quotient S}(x : Quotient PQ) 
         → ∀ {B a f q q'} 
         → qelim x {B} f q (nf PQ a) 
           ≡ qelim x {B} f q' (nf PQ a)
qelimIrr x {B} {a} {f} {q} {q'} = (qelim-β x {B} {a} {f} q) 
                                ▶ ⟨ qelim-β x {B} {a} {f} q' ⟩
-}

\end{code}

\emph{Exact quotients}
\begin{code}
{-
record QuE {A : Setoid}{PQ : pre-Quotient A}(QU : Quotient PQ) : Set₁ where
  constructor
    exact:_
  private
    _∼_　　= _≈_ A
    [_]　　= nf PQ
  field
    exact : ∀ {a b : ∣ A ∣} → [ a ] ≡ [ b ] → a ∼ b
open QuE
       
-}

\end{code}

\emph{Quotients as prequotients with a non-dependent eliminator (lift).}

\emph{(As in Hofmann's PhD dissertation.)}

\begin{code}
{-
record QuH {A : Setoid} (PQ : pre-Quotient A) : Set₁ where
  constructor
    lift:_lift-β:_qind:_
  private
    _∼_    = _≈_ A
    Q      = Q' PQ
    [_]    = nf PQ
  field
    lift   : {B : Set}
           → (f : ∣ A ∣ → B)
           → ((a b : ∣ A ∣) → (a ∼ b) → f a  ≡  f b)
           → Q → B
    lift-β : ∀ {B a f q} → lift {B} f q [ a ]  ≡ f a
    qind 　: (P : Q → Set)  
           → (∀ x → (p p' : P x) → p ≡ p')
           → (∀ a → P [ a ]) 
           → (∀ x → P x)

open QuH renaming (lift to lift' ; lift-β to lift-β')
-}
\end{code}

\emph{Definable quotients}
\begin{code}
 {-
record QuD {A : Setoid}(PQ : pre-Quotient A) : Set₁ where
  constructor
    emb:_complete:_stable:_
  private
    _∼_   = _≈_ A
    Q     = Q' PQ
    [_]   = nf PQ
  field
    emb      : Q → ∣ A ∣
    complete : ∀ a → emb [ a ] ∼ a
    stable   : ∀ q → [ emb q ] ≡ q
open QuD
-}
\end{code}

\emph{Relations between types of quotients:}

Below, we show the following, where the arrow → means "gives rise to" :

|QuH → Qu| (Proposition 3 in the paper)

|Quotient → QuH| (Reverse of Proposition 3)

|QuD → QuE| (A definable quotient is always exact)

|QuD → Qu|

|QuD → QuH| (Also a consequence of |QuD → Qu| and |Quotient → QuH|)

\begin{code}
{-
QuH→Quotient : {A : Setoid} → {PQ : pre-Quotient A}
       → (QuH PQ) → (Quotient PQ)
QuH→Quotient {A} {Q: Q []: [_] sound: sound}
       (lift: lift lift-β: β qind: qind) = 
  record 
    { qelim   = λ {B} → qelim₁ {B}
    ; qelim-β = λ {B} {a} {f} → qelim-β₁ {B} a f
    }
  where
    _∼_    = _≈_ A

    -- the dependent function f is made independent
    indep : {B : Q → Set}  → ((a : ∣ A ∣) → B [ a ]) → ∣ A ∣ → Σ Q B
    indep f a = [ a ] , f a

    indep-β : {B : Q → Set} 
            → (f : (a : ∣ A ∣) → B [ a ]) 
            → (∀ a b → (p : a ∼ b) → subst B (sound p) (f a) ≡ f b) 
            → ∀ a a' → (a ∼ a') → indep {B} f a ≡ indep f a'          
    indep-β {B} f q a a' p = (cong_,_ [ a ] [ a' ] (sound p) (f a))
                           ▶ ((λ b → [ a' ] , b) ⋆ (q a a' p))
    
    lift₀ : {B : Q → Set}
         → (f : (a : ∣ A ∣) → (B [ a ]))
         → ((a a' : ∣ A ∣) → (p : a ∼ a')
         → subst B (sound p)  (f a) ≡ f a')
         → Q → Σ Q B 
    lift₀ f q = lift (indep f) (indep-β f q)
                     
    qind₁ : {B : Q → Set}
         → (f : (a : ∣ A ∣) → B [ a ]) 
         → (q : ∀ a b → (p : a ∼ b) → subst B (sound p) (f a) ≡ f b) 
         → ∀ (c : Q) → proj₁ (lift₀ f q c) ≡ c
    qind₁ {B} f q = qind P heredity base 
      where
        f' : Q → Σ Q B
        f' = lift₀ f q
        P : Q → Set
        P c = proj₁ {_} {_} {Q} {B} (lift₀ f q c) ≡ c
        heredity : ∀ x → (p p' : P x) → p ≡ p' 
        heredity x p p' = ≡-prfIrr (proj₁ (lift₀ f q x)) x p p'  
        base : ∀ a → P [ a ]
        base a = proj₁ ⋆ β

    qelim₁  : { B : Q → Set }
           → (f : (a : ∣ A ∣) → (B [ a ]))
           → (∀ a b → (p : a ∼ b) → subst B (sound p) (f a) ≡ f b)
           → (c : Q) → B c 
    qelim₁ {B} f q c = subst B (qind₁ f q c)
                      (proj₂ {_} {_} {Q} {B} (lift₀ f q c))

    qelim-β₁ : ∀ {B} a f q → qelim₁ {B} f q [ a ] ≡ f a
    qelim-β₁ {B} a f q =
      (substIrr B (qind₁ f q [ a ]) 
        (cong-proj₁ {Q} {B} (lift₀ f q [ a ]) (indep f a) β) 
        (proj₂ {_} {_} {Q} {B} (lift₀ f q [ a ]))) ▶
      (cong-proj₂ {Q} {B} (lift₀ f q [ a ]) (indep f a) β)
\end{code}


\begin{code}
Qu→QuH : {S : Setoid} → {PQ : pre-Quotient S} 
       → (Quotient PQ) → (QuH PQ)
Qu→QuH {S} {Q: Q []: [_] sound: sound} (qelim: qelim qelim-β: β) =
  record 
  { lift   = λ {B} f s → qelim {λ _ → B} f (λ a b p 
           → (subFix (sound p) B (f a)) ▶ (s a b p))
  ; lift-β = λ {B} {a'} {f} {s} → β {λ _ → B} {a'} {f} (λ a b p 
           → (subFix (sound p) B (f a)) ▶ (s a b p))
  ; qind = λ P irr f
         → qelim {P} f (λ a b p → irr [ b ] (subst P (sound p) (f a)) (f b))
  }
  where
    subFix : ∀ {A : Set}{c d : A}(x : c ≡ d)(B : Set)(p : B)
           → subst (λ _ → B) x p ≡ p
    subFix refl _ _ = refl

\end{code}


\begin{code}

QuD→QuE : {A : Setoid}{PQ : pre-Quotient A}{QU : Quotient PQ} 
        → (QuD PQ) → (QuE QU)
QuD→QuE {A} {Q: Q []: [_] sound: _}
        (emb: emb complete: complete stable: _) =
  record { exact =  λ {a} {b} [a]≡[b] 
         → ⟨ complete a ⟩₀ 
           ▶₀ subst (λ x → x ∼ b) (emb ⋆ ⟨ [a]≡[b] ⟩) (complete b)
         }
    where
      _∼_   = _≈_ A
      ⟨_⟩₀   : Symmetric _∼_
      ⟨_⟩₀   = sym-s A
      _▶₀_  : Transitive _∼_
      _▶₀_  = trans-s A 

\end{code}


\begin{code}

QuD→Quotient : {S : Setoid} → {PQ : pre-Quotient S}
       → (QuD PQ) → (Quotient PQ)
QuD→Quotient {S} {Q: Q []: [_] sound: sound}
       (emb: ⌜_⌝ complete: complete stable: stable) = 
  record 
  { qelim   = λ {B} f _ a → subst B (stable a) (f ⌜ a ⌝)
  ; qelim-β = λ {B} {a} {f} s 
              → substIrr B (stable [ a ]) (sound (complete a)) (f ⌜ [ a ] ⌝) 
              ▶ s _ _ (complete a)
  }

\end{code}


\begin{code}

QuD→QuH : {S : Setoid} → {PQ : pre-Quotient S}
        → (QuD PQ) → (QuH PQ)
QuD→QuH {S} {Q: Q []: [_] sound: sound}
        (emb: ⌜_⌝ complete: complete stable: stable) =
  record 
  { lift   = λ f _ q → f ⌜ q ⌝
  ; lift-β = λ {B} {a} {f} {s} → s ⌜ [ a ] ⌝ a (complete a)
  ; qind   = λ P _ f → λ x → subst P (stable x) (f ⌜ x ⌝) 
  }

\end{code}

Or
\begin{code}

QuD→QuH' : {S : Setoid} → {PQ : pre-Quotient S}
         → (QuD PQ) → (QuH PQ)
QuD→QuH' {S} = Qu→QuH ∘ QuD→Quotient
-}
\end{code}


\end{document}