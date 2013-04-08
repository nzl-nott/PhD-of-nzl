{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check #-}


module GroupoidLaws where

open import Syntax
open import Relation.Binary.PropositionalEquality 
open import Relation.Binary.HeterogeneousEquality as ht using (≅-to-≡) renaming (_≅_ to _≋_; refl to hrefl)
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat

-- non-empty Context
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

NE = Σ Con Ty

preCon : NE → Con
preCon = proj₁

∥_∥ : NE → Con
∥_∥ = uncurry _,_

lastTy : (Γ : NE) → Ty (preCon Γ)
lastTy  = proj₂

lastTy' : (Γ : NE) → Ty ∥ Γ ∥
lastTy' (_ ,, A) = A +T A

lastVar' : (Γ : NE) → Var (lastTy' Γ)
lastVar' Γ = v0

--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

-- data isΩContr : NE → Set
{-
ΩNE : {Γ : Con} → isΩContr Γ → NE
-}
-- Globular Context

preΩContr = Σ[ ne ∶ NE ] Var (lastTy' ne)

-- the real ΩContr thing looks like this

ΩContr : preΩContr → NE
ΩContr ((Γ ,, A) ,, x) = (Γ , A , A +T A) ,, (var (vS v0) ≣ var v0)

{-
soundΩContr : (pC : preΩContr) → isContr ∥ ΩContr pC ∥
soundΩContr (proj₁ ,, pC) = ext {!soundContr!} {!!}

data isΩContr where
  c*  : isΩContr (ε , * , * , (var (vS v0) ≣ var v0))
  ext : {Γ : Con} →
        (isc : isΩContr Γ) → 
        (x : Var (lastTy' (ΩNE isc))) 
        → isΩContr (Γ , (lastTy' (ΩNE isc))) , (var (vS x) ≣ var v0))
-}
{-
ΩNE c* = ? -- isNE _ _
ΩNE (ext isc x) = ? -- isNE _ _

ΩContr = Σ Con isΩContr

soundΩ : ∀ {Γ} →  isΩContr Γ → isContr Γ
soundΩ c* = c*
soundΩ (ext iso x) = ext (soundΩ iso) x
-}
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

-- suspension for Con, Ty, Tm, _⇒_


-- Σ' symbol for suspension

-- ΣC' : NE → NE
ΣC : Con → Con
ΣT : {Γ : Con} → Ty Γ → Ty (ΣC Γ)
Σtm : {Γ : Con}(A : Ty Γ) → Tm A → Tm (ΣT A)
Σs : {Γ Δ : Con} → Γ ⇒ Δ → ΣC Γ ⇒ Δ

ΣC ε = ε , * , *  -- , (var (vS v0) ≣ var v0)
ΣC (Γ , A) = ΣC Γ , ΣT A

--given any Con we have *, give nany ΣC c , we have x = y

*' : {Γ : Con} → Ty (ΣC Γ)
*' {ε} = var (vS v0) ≣ var v0
*' {Γ , A} = *' {Γ} +T ΣT A

_≣'_ : {Γ : Con}{A : Ty Γ}(a b : Tm A) → Ty (ΣC Γ)
a ≣' b = Σtm _ a ≣ Σtm _ b

ΣT {Γ} * = *' {Γ}
ΣT (a ≣ b) = a ≣' b

ΣT[+T] : {Γ : Con}(A : Ty Γ)(B : Ty Γ) → ΣT A +T ΣT B ≡ ΣT (A +T B)
Σtm[+tm] : {Γ : Con}{A : Ty Γ}(a : Tm A)(B : Ty Γ) → Σtm _ a +tm ΣT B ≅ Σtm _ (a +tm B)

ΣT[+T] {Γ} (*) B = refl
ΣT[+T] {Γ} (_≣_ {A} a b) B = hom≡ (ΣT[+T] A B) (Σtm[+tm] a B) (Σtm[+tm] b B)

ΣT[Σs]T : {Γ Δ : Con}{A : Ty Δ} → (δ : Γ ⇒ Δ) → A [ Σs δ ]T ≡ ΣT (A [ δ ]T)

Σv : {Γ : Con}(A : Ty Γ) → Var A → Var (ΣT A)
Σv .(A +T A) (v0 {Γ} {A}) = subst Var (ΣT[+T] {_} A A) v0
Σv .(A +T B) (vS {Γ} {A} x {B}) = subst Var (ΣT[+T] {_} A B) (vS (Σv A x))

Σtm A (var x) = var (Σv A x)
Σtm .(A [ δ ]T) (JJ x δ A) = JJ x (Σs δ) A ⟦ ΣT[Σs]T δ ⟫



Σs • = {!!}
Σs (_,_ γ {A} a) = (Σs γ) , Σtm (A [ γ ]T) a ⟦ sym (ΣT[Σs]T γ) ⟫

ΣT[Σs]T {Γ} {Δ} {*} δ = {!!}
ΣT[Σs]T {Γ} {Δ} {a ≣ b} δ = {!!}

Σtm[+tm] {A = A} (var x) B = refl (var (vS (Σv A x))) ∾ (cohOpV (ΣT[+T] A B) -¹)
Σtm[+tm] (JJ x δ A) B = {!!}




--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

IdCm : ∀ Γ → Γ ⇒ Γ

lemIC : ∀ {Γ : Con}(A : Ty Γ) → A [ IdCm Γ ]T ≡ A
lemIC2 : ∀{Γ : Con}{A : Ty Γ}(x : Var A) →  x [ IdCm Γ ]V ≅ var x
lemIC3 : ∀{Γ Δ : Con}(δ : Γ ⇒ Δ) → δ ⊚ IdCm Γ ≡ δ
lemIC4 : ∀{Γ : Con}{A : Ty Γ}(a : Tm A) → a [ IdCm Γ ]tm ≅ a

IdCm ε = •
IdCm (Γ , A) = ((IdCm Γ) +S A) , var v0 ⟦ sym (trans ([+S]T A (IdCm Γ) A) (cong (λ x → x +T A) (lemIC A))) ⟫

lemIC {Γ} * = refl
lemIC {Γ} (a ≣ b) = hom≡ (lemIC _) (lemIC4 a) (lemIC4 b)

lemIC2 {.(Γ , A)} {.(A +T A)} (v0 {Γ} {A}) = cohOp
                                           (+T[,]T A (IdCm Γ +S A)
                                            (var v0 ⟦
                                             sym (trans ([+S]T A (IdCm Γ) A) (cong (λ x → x +T A) (lemIC A)))
                                             ⟫))
                                           ∾
                                           cohOp
                                           (sym
                                            (trans ([+S]T A (IdCm Γ) A) (cong (λ x → x +T A) (lemIC A))))
lemIC2 {.(Γ , B)} {.(A +T B)} (vS {Γ} {A} x {B}) = cohOp
                                                 (+T[,]T A (IdCm Γ +S B)
                                                  (var v0 ⟦
                                                   sym
                                                   (trans ([+S]T B (IdCm Γ) B) (cong (λ x₁ → x₁ +T B) (lemIC B)))
                                                   ⟫))
                                                 ∾ ([+S]V x (IdCm Γ) B ∾ cong+tm2 (lemIC A) (lemIC2 x))

lemIC3 • = refl
lemIC3 {Γ} (_,_ δ {A} a) = cm-eq (lemIC3 δ) (cohOp (sym ([⊚]T δ (IdCm Γ) A)) ∾ lemIC4 a)


lemIC4 {Γ} {A} (var x) = lemIC2 x

lemIC4 {Γ} {.(A [ δ ]T)} (JJ x δ A) = cohOp ([⊚]T δ (IdCm Γ) A) ∾ cong≅ (λ t → JJ x t A) (lemIC3 δ)


--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------



anyTypeInh : ∀{Γ} → {A : Ty Γ} → isContr Γ → Tm {Γ} A
anyTypeInh {A = A} ctr = JJ ctr (IdCm _)  A ⟦ lemIC _ ⟫
{- examples -}

Reflexive : NE → Set
Reflexive Γ = Tm {∥ Γ ∥} (var v0 ≣ var v0)

refl* : Reflexive (ε ,, *)
refl* = anyTypeInh c* -- this decides the type!!!

-- trans* : Tm {ε , x : *, y : *, p : hom * x y, z : *, home * y z} (hom * x z)
-- x : * , y : *, y ≡ x , z : * , z ≡ y --->  z ≡ x
-- x , y , y = x

-- x , y , y = x , y , y = y ---> y = x

transCon : Con
transCon = ε , * , * , (var (vS v0) ≣ var v0) , * , (var (vS (vS v0)) ≣  var v0)

{-
trans* : Tm {transCon} (lastTy' transCon ?)
trans* = anyTypeInh (ext (ext c* v0) (vS v0))
-}
-- tm-reflA : 
-- replacing * with refl

-- NE should be NE = Σ Con Ty

loopΩ-best : NE → NE
loopΩ-best (Γ ,, *) = ε  ,, *
loopΩ-best (Γ ,, (_≣_ {A} a b)) = let (Γ' ,, A') = loopΩ-best (Γ ,, A) in Γ' , A' , A' +T A' ,, (var (vS v0) ≣ var v0)

{-
loopΩ-best-SecondCase : NE → preΩContr
loopΩ-best-SecondCase (_ ,, *) = (ε ,, *) ,, v0
loopΩ-best-SecondCase (Γ ,, (_≣_ {A} a b)) = ΩContr (loopΩ-best-SecondCase (Γ ,, A)) ,, v0


loopΩ-best' : NE → NE
loopΩ-best' (Γ ,, *) = ε  ,, *
loopΩ-best' (Γ ,, (_≣_ {A} a b)) = ΩContr (loopΩ-best-SecondCase (Γ ,, A))

-}

loopΩ-Contr : (ne : NE) → isContr ∥ loopΩ-best ne ∥
loopΩ-Contr (Γ ,, *) = c*
loopΩ-Contr (Γ ,, _≣_ {A} a b) = ext (loopΩ-Contr (Γ ,, A)) v0

{-
loopΩ-Contr : (ne : NE) → isContr ∥ loopΩ-best' ne ∥
loopΩ-Contr (Γ ,, *) = c*
loopΩ-Contr (Γ ,, _≣_ {*} a b) = ext c* v0
loopΩ-Contr (Γ ,, _≣_ {_≣_ {A} a b} a₁ b₁) = ext (loopΩ-Contr (Γ ,, (a ≣ b))) v0
-}
-- loopΩ-best-SecondCase

loopΩ-refl : (ne : NE) → Reflexive (loopΩ-best ne)
loopΩ-refl ne = anyTypeInh (loopΩ-Contr ne)


-- important morphisms used to define "refl" for any types

_-v : ∀{Γ : Con}{A : Ty Γ} → Var (A +T A) → Var A
x -v = {!x!}


{-
∥_∥s : {Γ Δ : Con}{A : Ty Δ} → NEs  Γ Δ A → Γ ⇒ (Δ , A)
∥ γ ,, a ∥s = γ , var {!x§!}
-}


-- susTy : {Γ Δ : Con}(A : Ty Γ)(a b : Tm A)Ty Γ , A → Ty Γ , a ≣ b


transform : ∀ {Γ Δ : Con}(A : Ty Γ)(a b : Tm A) → (Γ , A) ⇒ Δ →  (Γ , (a ≣ b)) ⇒ Δ

susTm : {Γ Δ : Con}(A : Ty Γ)(a b : Tm A)(B : Ty Δ) → (γ : (Γ , A) ⇒ Δ) → Tm {Γ , A} (B [ γ ]T) → Tm {Γ , (a ≣ b)} (B [ transform A a b γ ]T)

transform A a b • = •
transform A a b (γ , a₁) = (transform A a b γ) , susTm A a b _ γ a₁

susTm A a b B • t = {!!}
susTm A a b B (γ , a₁) t = {!!}

refl-morphism-fst : (ne : NE) → ∥ ne ∥ ⇒ (preCon (loopΩ-best ne))
refl-morphism-fst (Γ ,, *) = • 
refl-morphism-fst (Γ ,, (_≣_ {A} a b)) = ((transform A a b (refl-morphism-fst (Γ ,, A)) , {!a +tm (a ≣ b)!}) , {!b!})  -- {!refl-morphism-best !} +S A , {!!}

tm-refl :  (ne : NE) → Tm {∥ ne ∥} (var v0 ≣ var v0)
tm-refl ne = loopΩ-refl ne [ (refl-morphism-fst ne) , {!var v0!} ]tm ⟦ {!!} ⟫

{-
  JJ (soundΩ {loop (a ≣ b)}
     (loopΩContr {A = a ≣ b})) 
     (cmToContr (a ≣ b)) 
     (var (lastVar' (loop (a ≣ b)) (ΩNE (loopΩContr {Γ} {a ≣ b}))) ≣ {! var (lastVar' (loop (a ≣ b)) {!!})!}) ⟦ {!!} ⟫


-}






---- it holds : A [ ? ]T ≡ B


{-
tm-refl {Γ} (_≣_ {A} a b) = refl*ind (recoverCon (makeCon (count-ty-lv A))) {!!}  {!!} {!!} [ {!!} ]tm



tm-refl (_≣_ {*} a b) = {!!} -- (tm-refl *) [ {!!} ]tm  ⟦ {!!} ⟫ -- refl*ab [ (• , b +tm (a ≣ b)) , a +tm (a ≣ b) , var v0 ]tm
tm-refl (_≣_ {a ≣ b} a₁ b₁) = {!!}
tm-refl * = refl* [ • , var v0 ]tm


-}
-- Γ , x : A ⊢ x ≣ x
-- Γ , x : * ⊢ x ≣ x
-- Γ , x : a ≣ b ⊢ x ≣ x
-- x ≡ refl ≡ refl ≡ x


{-

λ' : trans (refl , p) = p
...
-}
{- prove the laws of 2-groupoid and Eckman-Hilton -}

{-

 p q : refl a ≡ refl a 

1 = refl (refl a)

p ; q = (1 ; p) ; (q ; 1) = (1 ; q) ; (p ; 1)..... 

     p ; q = q ; p



-}