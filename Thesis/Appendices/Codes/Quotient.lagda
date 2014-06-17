\chapter{Set Quotients and Groupoid Quotients}

\begin{code}

module Quotient where

open import Data.Product
open import Function
open import Level using (_⊔_)
import Relation.Binary as RB

Setoid = RB.Setoid Level.zero Level.zero

open import Relation.Binary.PropositionalEquality as PE
  hiding ([_])

open import ThomasProperties

coerce : {A B : Set} → A ≡ B → A → B
coerce refl m = m

_respects_ : ∀{α β}{A : Set α}{B : Set β}(f : A → B) → (_~_ : A → A → Set α) → Set (α ⊔ β)
f respects _~_ = ∀ {a a'} → a ~ a' → f a ≡ f a'

isProp : (P : Set) → Set
isProp P =  {p p' : P} → p ≡ p'

isSet : (S : Set) → Set
isSet S = {a b : S} → isProp (a ≡ b)

subIrr : {S : Set}(isS : isSet S)
         {A : S → Set}{a b : S}(p q : a ≡ b){m : A a}
       → subst A p m ≡ subst A q m
subIrr isS p q = cong (λ p' → subst _ p' _) (isS {p = p} {p' = q})

subIrr2 : {S : Set}{A : Set}{a b : S}(p : a ≡ b){m : A}
       → subst (λ _ → A) p m ≡ m
subIrr2 refl = refl

\end{code}

\emph{Prequotients}

(Cone) Given a setoid, we can turn it into a pre-quotient which doesn't have too much practical meaning but served as a preparation for different kinds of quotient definitions.

\begin{code}


record pre-Quotient (S : Setoid) : Set₁ where
  open RB.Setoid S renaming (Carrier to A; _≈_ to _~_ ; refl to ~-refl; sym to ~-sym; trans to ~-trans)
  field
    Q   : Set
    [_] : A → Q
    [_]⁼ : [_] respects _~_
    QisSet : isSet Q

  open RB.Setoid S public renaming (Carrier to A; _≈_ to _~_ ; refl to ~-refl; sym to ~-sym; trans to ~-trans)
\end{code}

\emph{Quotients as prequotients with a non-dependent eliminator (lift).}

\emph{As in Hofmann's PhD dissertation.}

\begin{code}

record Hof-Quotient {S : Setoid}(PQ : pre-Quotient S) : Set₁ where
  open pre-Quotient PQ
  field
    lift   : {B : Set}
           → (f : A → B)
           → f respects _~_
           → Q → B

    lift-β : ∀ {B a f}(resp : f respects _~_) 
           → lift {B} f resp [ a ] ≡ f a

    qind   : ∀ (P : Q → Set)
           → (∀{x} → isProp (P x))
           → (∀ a → P [ a ])
           → (∀ x → P x)

\end{code}

\emph{Quotients as prequotients with a dependent eliminator.}


\begin{code}

record Quotient {S : Setoid}(PQ : pre-Quotient S) : Set₁ where
  open pre-Quotient PQ
  field
    qelim   : {B : Q → Set}
            → (f : (a : A) → B [ a ])
            → (∀ {a a'} → (p : a ~ a') → subst B [ p ]⁼ (f a) ≡ f a')
            → (q : Q) → B q
    qelim-β : ∀ {B a f}(resp : (∀ {a a'} → (p : a ~ a') → subst B [ p ]⁼ (f a) ≡ f a'))
            → qelim {B} f resp [ a ] ≡ f a

\end{code}

\emph{Exact} quotients

\begin{code}


isExact : {S : Setoid}{PQ : pre-Quotient S}(Qu : Quotient PQ) → Set
isExact {S} {PQ} Qu = ∀ {a b : A} → [ a ] ≡ [ b ] → a ~ b
  where open pre-Quotient PQ

record ExactQuotient {S : Setoid}(PQ : pre-Quotient S) : Set₁ where
  field
    Qu    : Quotient PQ
    exact : isExact Qu

\end{code}


\emph{Definable quotients}
\begin{code}
 
record def-Quotient {S : Setoid}(PQ : pre-Quotient S) : Set₁ where
  open pre-Quotient PQ
  field
    emb      : Q → A
    complete : ∀ a → emb [ a ] ~ a
    stable   : ∀ q → [ emb q ] ≡ q

  exact : ∀{a b} → [ a ] ≡ [ b ] → a ~ b
  exact {a} {b} p = ~-trans (~-sym (complete a)) (~-trans (subst (λ x → emb [ a ] ~ emb x) p ~-refl) (complete b))
\end{code}

\emph{Relations between types of quotients:}

Below, we show the following, where the arrow → means "gives rise to" :

|Hof-Quotient → Qu| (Proposition 3 in the paper)

|Quotient → Hof-Quotient| (Reverse of Proposition 3)

|def-Quotient → QuE| (A definable quotient is always exact)

|def-Quotient → Qu|

|def-Quotient → Hof-Quotient| (Also a consequence of |def-Quotient → Qu| and |Quotient → Hof-Quotient|)

\begin{code}

Σeq : {A : Set}{B : A → Set}{a a' : A}{b : B a}{b' : B a'}(p : a ≡ a') → subst B p b ≡ b' → (a , b) ≡ (a' , b')
Σeq refl refl = refl


ind2dep : ∀ {Q : Set}{B : Q → Set}
        → (f : Q → Σ Q B)
        → (∀ q → proj₁ (f q) ≡ q)
        → (q : Q) → B q
ind2dep {Q} {B} f id' q = subst B (id' q) (proj₂ (f q))


Hof-Quotient→Quotient : {S : Setoid} → {PQ : pre-Quotient S}
       → (Hof-Quotient PQ) → (Quotient PQ)
Hof-Quotient→Quotient {S} {PQ} QuH = 
  record 
    { qelim   = λ {B} f resp → proj₁ (qelim' f resp)

    ; qelim-β = λ {B} {a} {f} resp → proj₂ (qelim' f resp)
    }
  where
    open pre-Quotient PQ
    open Hof-Quotient QuH

    qelim' : {B : Q → Set}
           → (f : (a : A) → B [ a ])
           → (∀ {a a'} → (p : a ~ a') → subst B [ p ]⁼ (f a) ≡ f a')
           → Σ[ f^ ∶ ((q : Q) → B q) ] (∀ {a} → f^ [ a ] ≡ f a)
    qelim' {B} f resp =  f^ , f^-β
          where
-- turn f into independent function

           f₀ : A → Σ Q B
           f₀ a = [ a ] , f a
    
           resp₀ : f₀ respects _~_
           resp₀ p = Σeq [ p ]⁼ (resp p)

-- lift the independent function

           f' : Q → Σ Q B
           f' = lift f₀ resp₀

-- split the function into two id' and f^

           id' : Q → Q
           id' = proj₁ ∘ f'
           
           P : Q → Set
           P q = id' q ≡ q

           f'-β : {a : A} → f' [ a ] ≡ [ a ] , f a
           f'-β = lift-β _

           f'-sound : ∀{a} → id' [ a ] ≡ [ a ]
           f'-sound = cong proj₁ f'-β

           f'-sound' : ∀ {q} → id' q ≡ q
           f'-sound' {q} = qind P QisSet (λ _ → f'-sound) q

           f'-sound2 : ∀ {a} → subst B f'-sound (proj₂ (f' [ a ])) ≡ f a
           f'-sound2 = cong-proj₂ _ _ f'-β

           f^ : (q : Q) → B q
           f^ q = subst B (f'-sound') (proj₂ (f' q))
           
           f^-β : ∀ {a} → f^ [ a ] ≡ f a
           f^-β {a} = trans (subIrr QisSet f'-sound' f'-sound) f'-sound2


\end{code}


\begin{code}

Quotient→Hof-Quotient : {S : Setoid}{PQ : pre-Quotient S} 
       → (Quotient PQ) → (Hof-Quotient PQ)
Quotient→Hof-Quotient {S} {PQ} QU =
  record 
  { lift   = λ f resp → qelim f (resp' resp)
  ; lift-β = λ resp → qelim-β (resp' resp)
  ; qind = λ P isP f → qelim {P} f (λ _ → isP)
  }
  where
    open pre-Quotient PQ
    open Quotient QU

    resp' : {B : Set}{a a' : A}{f : A → B}(resp : f respects _~_)(p : a ~ a') → subst (λ _ → B) [ p ]⁼ (f a) ≡ f a'
    resp' resp p = trans (subIrr2 [ p ]⁼) (resp p)

\end{code}


\begin{code}

def-Quotient→Quotient : {S : Setoid}{PQ : pre-Quotient S}
       → (def-Quotient PQ) → (Quotient PQ)
def-Quotient→Quotient {S} {PQ} QuD = 
  record { qelim = λ {B} f resp q → subst B (stable q) (f (emb q))
         ; qelim-β = λ {B} {a} {f} resp → trans (subIrr QisSet (stable [ a ]) [ complete a ]⁼) (resp (complete a))
  }
    where
    open pre-Quotient PQ
    open def-Quotient QuD

\end{code}

\begin{code}


def-Quotient→Hof-Quotient : {S : Setoid} → {PQ : pre-Quotient S}
        → (def-Quotient PQ) → (Hof-Quotient PQ)
def-Quotient→Hof-Quotient {S} {PQ} QuD =
  record 
  { lift   = λ f _ → f ∘ emb
  ; lift-β = λ resp → resp (complete _)
  ; qind   =  λ P _ f _ → subst P (stable _) (f (emb _))
  }
  where
    open pre-Quotient PQ
    open def-Quotient QuD

def-Quotient→Hof-Quotient' : {S : Setoid}{PQ : pre-Quotient S}
         → (def-Quotient PQ) → (Hof-Quotient PQ)
def-Quotient→Hof-Quotient' = Quotient→Hof-Quotient ∘ def-Quotient→Quotient


def-Quotient→ExactQuotient : {S : Setoid}{PQ : pre-Quotient S}
        → (def-Quotient PQ) → ExactQuotient PQ
def-Quotient→ExactQuotient {S} {PQ} QuD =
  record { Qu = def-Quotient→Quotient QuD
         ; exact = exact
         }
  where
    open pre-Quotient PQ
    open def-Quotient QuD


Prp = Set

_⇔_ : (A B : Prp) → Prp
A ⇔ B = (A → B) × (B → A)

module PuImpEff
  (PropUni₁ : ∀ {p q : Prp} → (p ⇔ q) → p ≡ q)

  {S : Setoid}

  {PQ : pre-Quotient S}

  (QuH : Hof-Quotient PQ)

    where

  open pre-Quotient PQ
  open Hof-Quotient QuH

\end{code}

since the level is not taken into account when defining quotient lifting, we have to postulate extra functions

\begin{code}  
  postulate 
    lift₁ : { B : Set₁}  → 
            (f : A → B) → 
            (f respects _~_) → 
             Q → B

  postulate
    lift-β₁ : ∀ {B a f}{resp : (f respects _~_)} → lift₁ {B} f resp [ a ]  ≡ f a

  exact : ∀ a a' → [ a ] ≡ [ a' ] → a ~ a'
  exact a a' p = coerce P^-β (~-refl {a})
        where
          P : A → Prp
          P x = a ~ x

          P-resp : P respects _~_
          P-resp {b} {b'} bb' = PropUni₁ ((λ ab → ~-trans ab bb') , (λ ab' → ~-trans ab' (~-sym bb')))

          P^ : Q → Prp
          P^ = lift₁ P P-resp

          P^-β : P a ≡ P a'
          P^-β = trans (sym lift-β₁) (trans (cong P^ p) lift-β₁)

\end{code}