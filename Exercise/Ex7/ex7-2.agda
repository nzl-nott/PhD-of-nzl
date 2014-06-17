module ex7-2 where

open import Data.Product

infix 4 _≡_ 

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a


J : {A : Set}(P : (a b : A) → a ≡ b → Set)
    → ((a : A) → P a a refl)
    → (a b : A)(p : a ≡ b) → P a b p
J P m .b b refl = m b

id : {A : Set} → A → A
id a = a

subst :  {A : Set}(a b : A)(p : a ≡ b)
        (B : A → Set) → B a → B b
subst a b p B = J (λ a b _ → B a → B b) (λ _ → id) a b p

[_] : {A : Set}{a b : A} → a ≡ b → b ≡ a
[_] {A} {a} {b} = J (λ a b _ → b ≡ a) (λ _ → refl) a b


infix 5 _>=<_

_>=<_ : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
_>=<_ {A} {a} {b} {c} ab bc = subst b c bc (_≡_ a) ab


-- Groupoid law :


Λ : {A : Set}{a b : A}{p : a ≡ b} → refl >=< p ≡ p
Λ {A} {a} {b} {p} = J (λ a b p → J (λ a' b' _ → a ≡ a' → a ≡ b') (λ _ x → x) a b p refl ≡ p) (λ _ → refl) a b p

ρ : {A : Set}{a b : A}{p : a ≡ b} → p >=< refl ≡ p
ρ = refl

{-
record Bun (A : Set)(a d : A) : Set where
  constructor _,_,_,_,_
  field
    b : A
    c : A
    ab : a ≡ b
    bc : b ≡ c
    cd : c ≡ d



α : {A : Set}{a b c d : A}{ab : a ≡ b}{bc : b ≡ c}{cd : c ≡ d} → ab >=< (bc >=< cd) ≡ (ab >=< bc) >=< cd
α {A} {a} {b} {c} {d} {ab} {bc} {cd} = {!!} -- subst {Bun A a d} {!!} {!!} {!!} {!!} {!!}

-- Bun A a d = Σ[ b ∶ A ] (Σ[ c ∶ A ] (a ≡ b) × (b ≡ c) × (c ≡ d))
-}



Tri : (A : Set) (a d : A) → Set
Tri A a d = Σ[ x ∶ A ] (x ≡ d) × (a ≡ x)

fst : {A : Set}{a d : A}  → Tri A a d → A
fst (f , _) = f


snd : {A : Set}{a d : A}  → (t : Tri A a d) → fst t ≡ d 
snd (_ , s , _) = s

trd : {A : Set}{a d : A}  → (t : Tri A a d) → a ≡ fst t
trd (_ , _ , t) = t


α : {A : Set}{a b c d : A}{p : a ≡ b}{q : b ≡ c}{r : c ≡ d} → p >=< (q >=< r) ≡ (p >=< q) >=< r
α {A} {a} {b} {c} {d} {ab} {bc} {cd} = subst {Tri A a d} (b , (J (λ a' b' _ → b ≡ a' → b ≡ b') (λ _ → id) c d cd bc) , ab) (c , cd , (J (λ a' b' _ → a ≡ a' → a ≡ b') (λ _ → id) b c bc ab)) (J (λ b1 c1 bc1 → (b , {!!} , {!!}) ≡ (c1 , {!!} , {!!})) (λ a' → {!!}) b c bc) (λ tri → J (λ a' b' _ → a ≡ a' → a ≡ b') (λ _ → id) b d (J (λ a' b' _ → b ≡ a' → b ≡ b') (λ _ → id) c d cd bc) ab ≡ J (λ a' b' _ → a ≡ a' → a ≡ b') (λ _ → id) (fst tri) d (snd tri) (trd tri)) refl


--  (λ b1 c1 bc1 → (b1 , J (λ a' b' _ → b ≡ a' → b ≡ b') (λ _ → id) c d cd bc , ?) ≡ (c , cd , J (λ a' b' _ → a ≡ a' → a ≡ b') (λ _ → id) b c bc ab))

-- (b ,  (J (λ a' b' _ → b ≡ a' → b ≡ b') (λ _ → id) c d r q) , p)
-- (c , r                                                      , (J (λ a' b' _ → a ≡ a' → a ≡ b') (λ _ → id) b c q p)) 



ι : {A : Set}{a b : A}{p : a ≡ b} → [ p ]  >=< p ≡ refl
ι = {!!}