

\begin{code}

module GroupoidQuotient where

open import Relation.Binary.PropositionalEquality as PE
  hiding ([_])
open import Quotient
open import Data.Product
open ≡-Reasoning
\end{code}

The equivalence relation is not propositional but h-set.

\begin{code}

record Groupoid : Set₁ where
  infix 4 _~_
  infixl 5 _*_
  field
    Carrier : Set
    _~_     : Carrier → Carrier → Set
    id      : ∀{a} → a ~ a
    _⁻¹      : ∀{a b} → a ~ b → b ~ a
    _*_     : ∀{a b c} → a ~ b → b ~ c → a ~ c
    id₁     : ∀{a b}{p : a ~ b} → id * p ≡ p
    id₂     : ∀{a b}{p : a ~ b} → p * id ≡ p
    inv₁    : ∀{a b}{p : a ~ b} → p * p ⁻¹ ≡ id
    inv₂    : ∀{a b}{p : a ~ b} →  p ⁻¹ * p ≡ id
    assoc   : ∀{a b c d}{p : a ~ b}{q : b ~ c}{r : c ~ d}
            → (p * q) * r ≡ p * (q * r)
    isGrp   : ∀{a b}{p q : a ~ b} → isProp (p ≡ q)

  inv₂-id₁ : ∀{a b c}{p : a ~ b}{q : b ~ c} → p ⁻¹ * p * q ≡ q
  inv₂-id₁ = trans (cong (λ x → x * _) inv₂) id₁

  inv₁-id₂ : ∀{a b c}{p : a ~ b}{q : b ~ c} → p * (q * q ⁻¹) ≡ p
  inv₁-id₂ = trans (cong (λ x → _ * x) inv₁) id₂

  id-sym : ∀ {a} → id ⁻¹ ≡ id {a} 
  id-sym = begin
              id ⁻¹        ≡⟨ sym id₂ ⟩
              id ⁻¹ * id   ≡⟨ inv₂ ⟩
              id ∎

  sym-comp : ∀ {a b c}(p : a ~ b)(q : b ~ c) → (p * q) ⁻¹ ≡ q ⁻¹ * p ⁻¹
  sym-comp p q = begin
              (p * q) ⁻¹                           ≡⟨ sym inv₁-id₂ ⟩
              (p * q) ⁻¹ * (p * p ⁻¹)               ≡⟨ cong (λ x → (p * q) ⁻¹ * (x * p ⁻¹)) (sym inv₁-id₂) ⟩
              (p * q) ⁻¹ * (p * (q * q ⁻¹) * p ⁻¹)   ≡⟨ cong (λ x → (p * q) ⁻¹ * (x * p ⁻¹)) (sym assoc) ⟩
              (p * q) ⁻¹ * (p * q * q ⁻¹ * p ⁻¹)     ≡⟨ sym assoc ⟩
              (p * q) ⁻¹ * (p * q * q ⁻¹) * p ⁻¹     ≡⟨ cong (λ x → x * p ⁻¹) (sym assoc) ⟩
              (p * q) ⁻¹ * (p * q) * q ⁻¹ * p ⁻¹     ≡⟨ cong (λ x → x * p ⁻¹) inv₂-id₁ ⟩
              q ⁻¹ * p ⁻¹ ∎

isGroupoid : (S : Set) → Set
isGroupoid S = {a b : S} → isSet (a ≡ b)

record pre-GQuotient (G : Groupoid) : Set₁ where
  open Groupoid G renaming (Carrier to A)
  field
    Q   : Set
    [_] : A → Q
    [_]⁼ : [_] respects _~_
    QisGroupoid : isGroupoid Q
  open Groupoid G public renaming (Carrier to A)

record GQuotient {G : Groupoid}(PGQ : pre-GQuotient G) : Set₁ where
  open pre-GQuotient PGQ
  field
    qelim   : {B : Q → Set}
            → (f : (a : A) → B [ a ])
            → (∀ {a a'} → (p : a ~ a') → subst B [ p ]⁼ (f a) ≡ f a')
            → (q : Q) → B q
    qelim-β : ∀ {B a f}(resp : (∀ {a a'} → (p : a ~ a') → subst B [ p ]⁼ (f a) ≡ f a'))
            → qelim {B} f resp [ a ] ≡ f a



record ExactGQuotient {G : Groupoid}{PGQ : pre-GQuotient G}(GQu : GQuotient PGQ) : Set₁ where
  open pre-GQuotient PGQ
  field
    exact  : ∀{a b : A} → [ a ] ≡ [ b ] → a ~ b
    isInv₁ : ∀{a b}{p : a ~ b} → exact [ p ]⁼ ≡ p
    isInv₂ : ∀{a b}{p : [ a ] ≡ [ b ]} → [ exact p ]⁼ ≡ p



module UAImpEff
  (UA : ∀ {p q : Set} → (p ⇔ q) → p ≡ q)
  (G : Groupoid)
  (PGQ : pre-GQuotient G)
  (GQu : GQuotient PGQ)
    where
  open pre-GQuotient PGQ
  open GQuotient GQu
\end{code}

There is also an equivalence on the arrow level $\_\sim_{1}\_$ derived from $\_\sim\_$ (higher levels are trivial)

\begin{code}
  _~₁_ : ∀{a a' b b'} → a ~ a' → b ~ b' → (a ~ b → a' ~ b')
  _~₁_ p q r = p ⁻¹ * r * q

  _~₁I_ : ∀{a a' b b'} → a ~ a' → b ~ b' → (a' ~ b' → a ~ b)
  _~₁I_ p q r = p * r * q ⁻¹

  ~₁-equiv₁ : ∀{a a' b b'}(p : a ~ a')(q : b ~ b')(r : a ~ b)
           → (p ~₁I q) ((p ~₁ q) r) ≡ r
  ~₁-equiv₁ p q r = begin
             (p * ((p ⁻¹ * r) * q)) * q ⁻¹ ≡⟨ cong (λ x → x * q ⁻¹) (sym assoc) ⟩
             ((p * (p ⁻¹ * r)) * q) * q ⁻¹ ≡⟨ cong (λ x → x * q * q ⁻¹) (sym assoc) ⟩
             (((p * p ⁻¹) * r) * q) * q ⁻¹ ≡⟨ cong (λ x → x * q * q ⁻¹) (trans (cong (λ x → x * _) inv₁) id₁) ⟩
             (r * q) * q ⁻¹               ≡⟨ assoc ⟩
             r * (q * q ⁻¹)               ≡⟨ trans (cong (λ x → r * x) inv₁) id₂ ⟩
             r ∎

  ~₁-equiv₂ : ∀{a a' b b'}(p : a ~ a')(q : b ~ b')(r : a' ~ b')
           → (p ~₁ q) ((p ~₁I q) r) ≡ r
  ~₁-equiv₂ p q r = begin
             (p ⁻¹ * ((p * r) * q ⁻¹)) * q ≡⟨ cong (λ x → x * q) (sym assoc) ⟩
             ((p ⁻¹ * (p * r)) * q ⁻¹) * q ≡⟨ cong (λ x → x * q  ⁻¹ * q) (sym assoc) ⟩
             (((p ⁻¹ * p) * r) * q ⁻¹) * q ≡⟨ cong (λ x → x * q ⁻¹ * q) (trans (cong (λ x → x * _) inv₂) id₁) ⟩
             (r * q ⁻¹) * q               ≡⟨ assoc ⟩
             r * (q ⁻¹ * q)               ≡⟨ trans (cong (λ x → r * x) inv₂) id₂ ⟩
             r ∎

  ~₁-sound : ∀{a a' b b'} → a ~ a' → b ~ b' → (a ~ b) ≡ (a' ~ b')
  ~₁-sound p q = UA ((p ~₁ q) , (p ~₁I q))
\end{code}

Functorial property

\begin{code}
  _~₁_-id : ∀ {a}(r : a ~ a) → (id ~₁ id) r ≡ r
  _~₁_-id r = begin
          id ⁻¹ * r * id ≡⟨ id₂ ⟩
          id ⁻¹ * r      ≡⟨ cong (λ x → x * r) id-sym ⟩
          id * r         ≡⟨ id₁ ⟩
          r ∎

  _~₁_-comp : ∀ {a a' a'' b b' b''}(p : a ~ a')(q : b ~ b')
             (p' : a' ~ a'')(q' : b' ~ b'')(r : a ~ b)
           → ((p * p') ~₁ (q * q')) r ≡ (p' ~₁ q') ((p ~₁ q) r)
  _~₁_-comp p q p' q' r = begin
          (p * p') ⁻¹ * r * (q * q')   ≡⟨ cong (λ x → x * r * (q * q')) (sym-comp _ _) ⟩
          (p' ⁻¹ * p ⁻¹) * r * (q * q') ≡⟨ cong (λ x → x * (q * q')) assoc ⟩
          p' ⁻¹ * (p ⁻¹ * r) * (q * q') ≡⟨ sym assoc ⟩
          p' ⁻¹ * (p ⁻¹ * r) * q * q'   ≡⟨ cong (λ x → x * q') assoc ⟩
          p' ⁻¹ * (p ⁻¹ * r * q) * q'   ∎


  postulate 
    lift₁ : { B : Set₁} 
            (f : A → B)
            (f-resp : f respects _~_)
          → Q → B

  postulate
    lift-β₁ : ∀ {B a f}
              {f-resp : f respects _~_}
            → lift₁ {B} f f-resp [ a ]  ≡ f a

  exact : ∀ {a a'} → [ a ] ≡ [ a' ] → a ~ a'
  exact {a} {a'} eq = coerce P^-β (id {a})
        where
          P : A → Set
          P x = a ~ x
\end{code}
Functorial
\begin{code}
          P₁ : ∀{b c} → b ~ c → (P b → P c)
          P₁ bc ab = ab * bc

          P₁-id : ∀{b}{r : P b} → P₁ id r ≡ r
          P₁-id = id₂

          P₁-comp : ∀{b c d}{p : b ~ c}{q : c ~ d}{r : P b} → P₁ (p * q) r ≡ P₁ q (P₁ p r)

          P₁-comp = sym assoc
\end{code}


We didn't write the equivalence proof explicitly i.e.\ isEquivalence (P₁ x).

\begin{code}
          P-resp : P respects _~_
          P-resp {b} {b'} bb' = UA (P₁ bb' , P₁ (bb' ⁻¹))

          P^ : Q → Prp
          P^ = lift₁ P P-resp

          P^-β : P a ≡ P a'
          P^-β = trans (sym lift-β₁) (trans (cong P^ eq) lift-β₁)


-- coerce (trans (sym lift-β₁) (trans (cong (lift₁ P P-resp) [ p ]⁼) lift-β₁)) (id {a}) ≡ p
--  isInv₁ : ∀{a b}{p : a ~ b} → exact [ p ]⁼ ≡ p
--  isInv₁ {p = p} = {!!}

--  isInv₂ : ∀{a b}{p : [ a ] ≡ [ b ]} → [ exact p ]⁼ ≡ p


\end{code}