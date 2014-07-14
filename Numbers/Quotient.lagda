\documentclass[a4paper,12pt]{article}

\usepackage[utf8x]{inputenc}
\usepackage{ucs}
\usepackage{cite}
\usepackage{MnSymbol}

\begin{document}

\section{Appendix}

\begin{code}

module Quotient where

open import Data.Product
open import Function
import Level
import Relation.Binary as RB

Setoid = RB.Setoid Level.zero Level.zero

open import Relation.Binary.PropositionalEquality as PE
  hiding ([_])

open import ThomasProperties


record ′_isProp′ (A : Set) : Set where
  field
    isProp : ∀ (a b : A) → a ≡ b
open ′_isProp′

record ′_isSet′ (Q : Set) : Set where
  field
    isSet : ∀{p q : Q} → ′ p ≡ q isProp′
open  ′_isSet′

record  ′_isPredicate′ {A : Set}(P : A → Set) : Set where
  field
    isPred : ∀ x → ′ (P x) isProp′
open ′_isPredicate′

subst-Irr : {A : Set}(P : A → Set) → ′ P isPredicate′
          → {a b : A}{x : P a}{p q : a ≡ b} → subst P p x ≡ subst P q x
subst-Irr P isP {a} {b} = isProp (isPred isP b) _ _


subst-Irr2 : {A : Set}(B : A → Set)
          → {a b : A}{x : B a}(p q : a ≡ b) → ′ A isSet′ → subst B p x ≡ subst B q x
subst-Irr2 B p q isS = cong (λ y → subst B y _) (isProp (isSet isS) p q) 

subst-Irr3 :  {A B : Set}
          → {a b : A}{x : B}(p : a ≡ b) → subst (λ _ → B) p x ≡ x
subst-Irr3 refl = refl

--setoid to set morphism

record _sd→s_ (S : Setoid) (B : Set) : Set where
  open RB.Setoid S renaming (Carrier to A; refl to ≈refl; sym to ≈sym; trans to ≈trans)
  field
    fun : A → B
    fun-correct :  ∀ {a b : A} → a ≈ b → fun a ≡ fun b
open _sd→s_ using () renaming (fun to apply; fun-correct to sound)

\end{code}

\emph{Prequotients}

(Cone) Given a setoid, we can turn it into a pre-quotient which doesn't have too much practical meaning but served as a preparation for different kinds of quotient definitions.

\begin{code}


record pre-Quotient (S : Setoid) : Set₁ where
  field
    Q      : Set
    Set-Q  : ′ Q isSet′
    nf     : S sd→s Q
  open RB.Setoid S public renaming (Carrier to A; refl to ≈refl; sym to ≈sym; trans to ≈trans)
  open ′_isSet′ Set-Q public renaming (isSet to QisSet)
  open _sd→s_ nf public renaming (fun to [_] ; fun-correct to nf-sound)

\end{code}

\emph{Quotients as prequotients with a non-dependent eliminator (lift).}

\emph{(As in Hofmann's PhD dissertation.)}

\begin{code}

record QuotientHoffmann {S : Setoid}(PQ : pre-Quotient S) : Set₁ where
  open pre-Quotient PQ
  field
    lift   : {B : Set}
           → (f : S sd→s B)
           → Q → B
    lift-β : ∀ {B a f} → lift {B} f [ a ] ≡ apply f a -- any f : S → B is factorizable as [_] and lift f : Q → B

    qind 　: (P : Q → Set)  
           → ′ P isPredicate′
           → (∀ a → P [ a ]) 
           → (∀ x → P x) -- ∀ x → ∃ a , x ≡ [ a ], no redandency in Q

\end{code}

\emph{Quotients as prequotients with a dependent eliminator.}
colimit


\begin{code}


record dep-fun {S : Setoid}
               (PQ : pre-Quotient S)(B : pre-Quotient.Q PQ → Set) : Set where
  open pre-Quotient PQ
  field
    fun : (a : A) → B [ a ]
    fun-correct : {a b : A} → (p : a ≈ b) → subst B (nf-sound p) (fun a) ≡ fun b
open dep-fun using () renaming (fun to dapply; fun-correct to dsound)


dep2ind : ∀  {S : Setoid}{PQ : pre-Quotient S}{B : pre-Quotient.Q PQ → Set} 
        → dep-fun PQ B 
        → S sd→s Σ (pre-Quotient.Q PQ) B
dep2ind {S} {PQ} f = record { fun = λ x → [ x ] , dapply f x; fun-correct = λ p → Σeq-split (nf-sound p) (dep-fun.fun-correct f p) }
  where
    open pre-Quotient PQ

ind2dep : ∀ {S : Setoid}{PQ : pre-Quotient S}{B : Set}
        → S sd→s B
        → dep-fun PQ (λ _ → B)
ind2dep {PQ = PQ} f = record { fun = fun ; fun-correct = λ p → trans (subst-Irr3 (_sd→s_.fun-correct (pre-Quotient.nf PQ) p)) (fun-correct p) }
  where
    open _sd→s_ f

record Quotient {S : Setoid}(PQ : pre-Quotient S) : Set₁ where
  open pre-Quotient PQ
  field
    qelim   : {B : Q → Set}
            → dep-fun PQ B
            → (q : Q) → B q
    qelim-β : ∀ {B a f} → qelim {B} f [ a ] ≡ dapply f a

\end{code}

\emph{Exact quotients}
\begin{code}

record ExactQuotient {S : Setoid}(PQ : pre-Quotient S) : Set₁ where
  open pre-Quotient PQ
  field
    Qu    : Quotient PQ
    exact : ∀ {a b : A} → [ a ] ≡ [ b ] → a ≈ b

\end{code}


\emph{Definable quotients}
\begin{code}
 
record DefinableQuotient {S : Setoid}(PQ : pre-Quotient S) : Set₁ where
  open pre-Quotient PQ
  field
    emb      : Q → A
    complete : ∀ a → emb [ a ] ≈ a
    stable   : ∀ q → [ emb q ] ≡ q

\end{code}

\emph{Relations between types of quotients:}

Below, we show the following, where the arrow → means "gives rise to" :

|QuotientHoffmann → Qu| (Proposition 3 in the paper)

|Quotient → QuotientHoffmann| (Reverse of Proposition 3)

|DefinableQuotient → QuE| (A definable quotient is always exact)

|DefinableQuotient → Qu|

|DefinableQuotient → QuotientHoffmann| (Also a consequence of |DefinableQuotient → Qu| and |Quotient → QuotientHoffmann|)

\begin{code}

QuotientHoffmann→Quotient : {S : Setoid} → {PQ : pre-Quotient S}
       → (QuotientHoffmann PQ) → (Quotient PQ)
QuotientHoffmann→Quotient {S} {PQ} QUH = 
  record 
    { qelim   = qelim₁
    ; qelim-β = λ {B} {a} {f} → trans (subst-Irr2 B (lift-d-β f [ a ])
                                         (cong-proj₁ (ld f [ a ]) (apply (dep2ind f) a) lift-β)
                                         Set-Q) (cong-proj₂ _ _ (lift-β {a = a} {dep2ind f}))
    }
  where
    open pre-Quotient PQ
    open QuotientHoffmann QUH

    
    ld   : {B : Q → Set}(f : dep-fun PQ B)(c : Q) → Σ Q B
    ld f = lift (dep2ind f)

    ldcom : {B : Q → Set}(f : dep-fun PQ B)(c : Q) → Set
    ldcom f c = proj₁ (ld f c) ≡ c

    lift-d-β : {B : Q → Set}
             → (f : dep-fun PQ B)
             → (c : Q) 
             → ldcom f c
    lift-d-β f c = qind (ldcom f) (record {isPred = λ x → QisSet}) (λ a → cong-proj₁ _ _ (lift-β {a = a} {dep2ind f})) c
    
    qelim₁  : {B : Q → Set}
           → dep-fun PQ B
           → (c : Q) → B c 
    qelim₁ {B} f c = subst B (lift-d-β f c)
                   (proj₂ (lift (dep2ind f) c))

\end{code}


\begin{code}

Quotient→QuotientHoffmann : {S : Setoid} → {PQ : pre-Quotient S} 
       → (Quotient PQ) → (QuotientHoffmann PQ)
Quotient→QuotientHoffmann {S} {PQ} QU =
  record 
  { lift   = qelim ∘ ind2dep
  ; lift-β = qelim-β
  ; qind = λ P isP f → qelim {P} (record { fun = f; fun-correct = λ p → isProp (isPred isP _) _ _})
  }
  where
    open pre-Quotient PQ
    open Quotient QU

\end{code}


\begin{code}

DefinableQuotient→Quotient : {S : Setoid}{PQ : pre-Quotient S}
       → (DefinableQuotient PQ) → (Quotient PQ)
DefinableQuotient→Quotient {S} {PQ} QUD = 
  record { qelim = λ {B} f q → subst B (stable q) (dapply f (emb q))
         ; qelim-β = λ {B} {a} {f} → trans (subst-Irr2 B (stable [ a ]) (nf-sound (complete a)) Set-Q) (dep-fun.fun-correct f (complete a))
  }
    where
    open pre-Quotient PQ
    open DefinableQuotient QUD

\end{code}

\begin{code}

-- the older proof with QU as assumption is actually wrong!

DefinableQuotient→ExactQuotient : {A : Setoid}{PQ : pre-Quotient A} -- {QU : Quotient PQ} 
        → (DefinableQuotient PQ) → ExactQuotient PQ
DefinableQuotient→ExactQuotient {A} {PQ} QUD =
  record { Qu = DefinableQuotient→Quotient QUD
         ; exact = λ {a} {b} p → ≈trans (≈sym (complete a)) (≈trans (id-eq (cong emb p)) (complete b))
         }
  where
    open pre-Quotient PQ
    open DefinableQuotient QUD

    id-eq : ∀{a b} → a ≡ b → a ≈ b
    id-eq refl = ≈refl 

\end{code}



\begin{code}

DefinableQuotient→QuotientHoffmann : {S : Setoid} → {PQ : pre-Quotient S}
        → (DefinableQuotient PQ) → (QuotientHoffmann PQ)
DefinableQuotient→QuotientHoffmann {S} {PQ} QUD =
  record 
  { lift   = λ f → apply f ∘ emb
  ; lift-β = λ {B} {a} {f} →  sound f {emb [ a ]} {a} (complete a)
  ; qind   =  λ P _ f → λ x → subst P (stable x) (f (emb x))
  }
  where
    open pre-Quotient PQ
    open DefinableQuotient QUD

\end{code}

Or

\begin{code}

DefinableQuotient→QuotientHoffmann' : {S : Setoid}{PQ : pre-Quotient S}
         → (DefinableQuotient PQ) → (QuotientHoffmann PQ)
DefinableQuotient→QuotientHoffmann' = Quotient→QuotientHoffmann ∘ DefinableQuotient→Quotient

\end{code}


\end{document}