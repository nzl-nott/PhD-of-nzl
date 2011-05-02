module ThomasProperties where
-- name to be changed, this is a bunch of auxiliary definitions added by need.

open import Algebra
open import Data.Function
open import Data.Nat
open import Data.Nat.Properties as Nat
private
   module N = CommutativeSemiring Nat.commutativeSemiring

open import Data.Product

open import Level

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core

open import Data.Vec

open ≡-Reasoning
open SemiringSolver


data Image_∋_ {A B : Set}(f : A → B) : B → Set where -- from Ulf Norell, http://www.springerlink.com/content/8x0h38858233vn26/
      im : (x : A) → Image f ∋ f x

subst∘const : {A B : Set} → {a b : A} → {u : B} → (q  : a ≡ b) → subst (λ _ →  B) q u ≡ u
subst∘const refl = refl

cong_,_ : {A : Set } {B : A → Set} → (a a' : A) → (p : a ≡ a') →  (b : B a)  →  _,_ {A = A} {B = B} a b  ≡ a' , subst B p b
cong_,_ a .a refl b = refl  

cong'_,_ : {A : Set } {B : A → Set} → (a : A) →  (b b' : B a) → ( q : b ≡ b') →  _,_ {A = A} {B = B} a b  ≡ a , b'
cong'_,_ a b .b refl = refl

cong-proj₁ : {A : Set } {B : A → Set} → (x x' : Σ A B) → (p : x ≡ x') → proj₁ x ≡ proj₁ x'
cong-proj₁ .x' x' refl = refl

cong-proj₂ : {A : Set } {B : A → Set} → (x x' : Σ A B) → (p : x ≡ x') →  subst B (cong-proj₁ x x' p) (proj₂ {A = A} {B = B} x) ≡ proj₂ {A = A} {B = B} x'
cong-proj₂ .x' x' refl = refl

-- aa : {A : Set } {B : A → Set} → (a : A) → (b b' : B a) → (p : _,_ {A} {B} a b ≡ (a , b')) → b ≡ b'
-- aa a .b' b' refl = refl






≡-prfIrr : {A : Set} → (a a' : A) → (p p' : a ≡ a') → p ≡ p'
≡-prfIrr .a' a' refl refl = refl



substIrr : {A : Set} → {a a' : A} → (B : A → Set) → ( p p' : a ≡ a') → (x : B a) → subst B p x ≡ subst B p' x
substIrr B0 refl refl x = refl

-- Some notation to shorten simple proofs or make them more human readable without using heavy  equational reasoning (begin ... ) 
infixr 41  _⋆_
infixr 40  _▶_

_▶_ : {a : Set} → Transitive {A = a} _≡_
_▶_ = trans 

⟨_⟩ :  {a : Set} → Symmetric {A = a} _≡_
⟨_⟩ = sym

Congruential : ({a : Set} → Rel a zero) → Set1
Congruential ∼ = ∀ {a b} → (f : a → b) → f Preserves ∼ ⟶ ∼

_⋆_ : Congruential _≡_
_⋆_ = cong


_≡+≡_ : {a a' b b' : ℕ} → a ≡ a' → b ≡ b' → a + b ≡ a' + b'
_≡+≡_ =  cong₂ _+_

_≡∷≡_ :  ∀ {n} {A : Set} → {a b : A} → {as bs : Vec A n} → a ≡ b → as ≡ bs → a ∷ as ≡ b ∷ bs
_≡∷≡_ = cong₂ _∷_

-- Other abreviations
_, : {A : Set} → {B : Set} → B → A →  A × B
_, = flip _,_ 

≡⇒≈ : {A : Set} → {_≈_ : Rel A zero}  → {p : Reflexive _≈_} → _≡_ ⇒ _≈_
≡⇒≈ {A} {_≈_} {p} refl = p

_Preserves'_ : ∀ {a} → (a → a) → Rel a zero → Set
f Preserves' ∼ = f Preserves ∼ ⟶ ∼ 

_Preserves₂'_ : ∀ {a} → (a → a → a) → Rel a zero → Set
+ Preserves₂' ∼  = + Preserves₂ ∼ ⟶ ∼ ⟶ ∼

_₁ : ∀ {A B} → Σ A B → A
_₁ = proj₁

_₂ : ∀ {A B} → (p : Σ A B) → B (proj₁ p)
_₂ = proj₂

ℕ² : Set
ℕ² = ℕ × ℕ


-- Useful functions
split : {A B : Set } → {f₁ f₂ : A → B}  → (∀ (a₀ : A) → f₁ a₀ ≡ f₂ a₀) → (a : A × A) → (f₁ (a ₁) , f₁ (a ₂)) ≡ (f₂ (a ₁) , f₂ (a ₂)) 
split p a = cong₂ _,_ (p (a ₁)) (p (a ₂)) 

split₂ : {A B C : Set } →  {f₁ f₂ : A → B → C} → (∀ (a₀ : A) (b₀ : B) → f₁ a₀ b₀  ≡ f₂ a₀ b₀) → (a : A × A) →  (b : B × B) → (f₁ (a ₁) (b ₁) , f₁ (a ₂) (b ₂)) ≡ (f₂ (a ₁) (b ₁) , f₂ (a ₂) (b ₂)) 
split₂ p a b  = cong₂ _,_ (p (a ₁) (b ₁)) (p (a ₂) (b ₂)) 

split₃ : {A B C D : Set } →  {f₁ f₂ : A → B → C → D} → (∀ (a₀ : A) (b₀ : B) (c₀ : C) → f₁ a₀ b₀ c₀  ≡ f₂ a₀ b₀ c₀) → (a : A × A) →  (b : B × B) → (c : C × C) → (f₁ (a ₁) (b ₁)  (c ₁), f₁ (a ₂) (b ₂) (c ₂)) ≡ (f₂ (a ₁) (b ₁) (c ₁), f₂ (a ₂) (b ₂) (c ₂)) 
split₃ p a b c  = cong₂ _,_ (p (a ₁) (b ₁) (c ₁)) (p (a ₂) (b ₂) (c ₂)) 


-- General basic lemmas about natural numbers
m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n 0       n = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

suc-injective : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-injective {m} {n} p = cong (flip _∸_ 1) p 

lem₁ :  ∀ a b c d  →  (a + b) + (c + d) ≡ (a + c) + (b + d)
lem₁ = solve 4 (λ a b c d → (a :+ b) :+ (c :+ d)  :=  (a :+ c) :+ (b :+ d)) refl

lem₃ : ∀ k₁ k₂ l₁ l₂ m₁ m₂ n₁ n₂ →  k₁ + l₂ ≡ l₁ + k₂  →  m₁ + n₂ ≡ n₁ + m₂  → (k₁ + m₁) + (l₂ + n₂) ≡ (l₁ + n₁) + (k₂ + m₂)
lem₃ k₁ k₂ l₁ l₂ m₁ m₂ n₁ n₂ p q = lem₁ k₁ m₁ l₂ n₂  ▶  cong₂ _+_ p q   ▶   lem₁ l₁ k₂ n₁ m₂  

lem₄ : ∀ m₁ m₂ n₁ n₂ →  m₁ + n₂ ≡ n₁ + m₂  → m₂ + n₁ ≡ n₂ + m₁
lem₄ m₁ m₂ n₁ n₂ p = N.+-comm m₂ n₁  ▶  ⟨ p ⟩  ▶  N.+-comm m₁ n₂  




{-

    begin
    ?
     ≡⟨ ? ⟩
    ?
     ≡⟨ ? ⟩
    ?
     ≡⟨ ? ⟩ 
    ?
     ≡⟨ ? ⟩
    ?
    ∎
-}