module nuo2-3 where

-- TTI = implement subst, postulate ext and idUni.

data Id (A : Set) : A → A → Set where
  refl : (a : A) → Id A a a

subst : (A : Set)(a b : A)(p : Id A a b)
        (B : A → Set) → B a → B b
subst A .b b (refl .b) B x = x


sym : (A : Set) → (a b : A) → Id A a b → Id A b a
sym A a b p = subst A a b p (λ b' → Id A b' a) (refl a)

postulate idUni : (A : Set)(a : A)(p : Id A a a) → Id (Id A a a) p (refl a)


postulate
  ext : (A : Set)(B : A → Set)(f g : (x : A) → B x)
        → ((x : A) → Id (B x) (f x) (g x)) 
        → Id ((x : A) → B x) f g


-- encode the example in the beginning section 2 in Agda

data Bool : Set where
  true : Bool
  false : Bool

if' : (P : Bool → Set) → (b : Bool) →
        (T : Id Bool b true → P true)
        (F : Id Bool b false → P false) → P b
if' P true T _ = T (refl true)
if' P false _ F = F (refl false)


data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

data Loc : Set where
  loc : Loc

data ⊥ : Set where

data Dec (A : Set) : Set where
  yes : A → Dec A
  no : (A → ⊥) → Dec A

dec : (l l' : Loc) → Dec (Id Loc l l')
dec l l' = {!l!}

eq : Loc → Loc → Bool
eq l l' with dec l l'
eq .l' l' | yes (refl .l') = true
eq l l' | no _ = false

eq' : (l : Loc) → (l' : Loc) → (Id Loc l l') + ((Id Loc l l') → ⊥)
eq' l l' with dec l l'
eq' l l' | yes y = inl y
eq' l l' | no y = inr y

eq-correct-1 : (l l' : Loc) → Id Loc l l' → Id Bool (eq l l') true
eq-correct-1 l l' e with dec l l'
eq-correct-1 .l' l' e | yes (refl .l') = refl true
eq-correct-1 l l' e | no y with y e
eq-correct-1 l l' e | no y | ()

-- subst Loc l l' e (λ x → Id Bool (eq x l') true) ({!refl!})

eq-correct-2 : (l l' : Loc) → Id Bool (eq l l') true → Id Loc l l'
eq-correct-2 l l' e with dec l l'
eq-correct-2 .l' l' e | yes (refl .l') = refl l'
eq-correct-2 l l' () | no y


eq-wrong-1 : (l l' : Loc) → (Id Loc l l' → ⊥) → Id Bool (eq l l') false
eq-wrong-1 l l' e with dec l l'
eq-wrong-1 l l' e | yes y with e y
eq-wrong-1 l l' e | yes y | ()
eq-wrong-1 l l' e | no y = refl false

data Data (l : Loc) : Set where

Store = (l : Loc) → (Data l) 

update : (l₀ : Loc)(d : Data l₀)(s : Store) → Store
update l₀ d s l = if' (λ x → Data l) (eq l₀ l)
  (λ x → subst Loc l₀ l (eq-correct-2 l₀ l x) Data d) (λ x → s l)

update-type = (l₀ : Loc)(d : Data l₀)(s : Store) → Store


update-spec   : update-type → Set
update-spec f = ((l₀ : Loc)(d : Data l₀)(s : Store) → Id (Data l₀) (f l₀ d s l₀) d) 
  × ( (l₀ : Loc)(d : Data l₀)(l : Loc)(s : Store) → ((Id Loc l l₀) → ⊥) → Id (Data l) (f l₀ d s l) (s l))

up-correct : update-spec update
up-correct =
  (λ l₀ d s → subst Bool true (eq l₀ l₀) (sym Bool (eq l₀ l₀) true (eq-correct-1 l₀ l₀ (refl l₀))) (λ e → Id (Data l₀) (if' (λ x → Data l₀) e (λ x → subst Loc l₀ l₀ (refl l₀) Data d) (λ x → s l₀)) d) (refl d)) ,
  (λ l₀ d l s x → subst Bool (eq l₀ l) false (eq-wrong-1 l₀ l (λ x' → x (sym Loc l₀ l x'))) (λ e → Id (Data l) (if' (λ x' → Data l) e (λ x' → subst Loc l₀ l (eq-correct-2 l₀ l x') Data d) (λ x' → s l)) (s l)) (refl (s l)))

