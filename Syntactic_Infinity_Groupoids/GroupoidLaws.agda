module GroupoidLaws where

open import Syntax renaming (hom to _≣_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality as ht using (≅-to-≡) renaming (_≅_ to _≋_; refl to hrefl)

open import Data.Nat

{- examples -}

cong+tm2 : ∀ {Γ : Con}{A B C : Ty Γ}{a : Tm A}{b : Tm B} → A ≡ B → a ≅ b → a +tm C ≅ b +tm C
cong+tm2 {Γ} {.B} {B} {C} {.b} {b} refl (refl .b) = refl _

refl* : Tm {ε , *} (var v0 ≣ var v0)
refl* = JJ c* (• , (var v0)) (var v0 ≣ var v0)


IdCm : ∀ Γ → Γ ⇒ Γ

lemIC : ∀ {Γ : Con}(A : Ty Γ) → A [ IdCm Γ ]T ≡ A
lemIC2 : ∀{Γ : Con}{A : Ty Γ}(a : Tm A) → a [ IdCm Γ ]tm ≅ a

IdCm ε = •
IdCm (Γ , A) = ((IdCm Γ) +S A) , var v0 ⟦ sym (trans ([+S]T A (IdCm Γ) A) (cong (λ x → x +T A) (lemIC A))) ⟫

lemIC {Γ} * = refl
lemIC {Γ} (a ≣ b) = hom≡ (lemIC _) (lemIC2 a) (lemIC2 b)




lemIC3 : ∀{Γ : Con}{A : Ty Γ}(x : Var A) →  x [ IdCm Γ ]V ≅ var x
lemIC3 {.(Γ , A)} {.(A +T A)} (v0 {Γ} {A}) = cohOp
                                           (+T[,]T A (IdCm Γ +S A)
                                            (var v0 ⟦
                                             sym (trans ([+S]T A (IdCm Γ) A) (cong (λ x → x +T A) (lemIC A)))
                                             ⟫))
                                           ∾
                                           cohOp
                                           (sym
                                            (trans ([+S]T A (IdCm Γ) A) (cong (λ x → x +T A) (lemIC A))))
lemIC3 {.(Γ , B)} {.(A +T B)} (vS {Γ} {A} x {B}) = cohOp
                                                 (+T[,]T A (IdCm Γ +S B)
                                                  (var v0 ⟦
                                                   sym
                                                   (trans ([+S]T B (IdCm Γ) B) (cong (λ x₁ → x₁ +T B) (lemIC B)))
                                                   ⟫))
                                                 ∾ ([+S]V x (IdCm Γ) B ∾ cong+tm2 (lemIC A) (lemIC3 x))

lemIC4 : ∀ {Γ Δ : Con}(δ : Γ ⇒ Δ) → δ ⊚ IdCm Γ ≡ δ
lemIC4 • = refl
lemIC4 {Γ} (_,_ δ {A} a) = cm-eq (lemIC4 δ) (cohOp (sym ([⊚]T δ (IdCm Γ) A)) ∾ lemIC2 a)


lemIC2 {Γ} {A} (var x) = lemIC3 x

lemIC2 {Γ} {.(A [ δ ]T)} (JJ x δ A) = cohOp ([⊚]T δ (IdCm Γ) A) ∾ cong≅ (λ t → JJ x t A) (lemIC4 δ)


-- trans* : Tm {ε , x : *, y : *, p : hom * x y, z : *, home * y z} (hom * x z)
-- x : * , y : *, y ≡ x , z : * , z ≡ y --->  z ≡ x
-- x , y , y = x

-- x , y , y = x , y , y = y ---> y = x

trans* : Tm {ε , * , * , (var v0 ≣ var (vS v0)) , * , var v0 ≣ var (vS (vS v0))}  (var (vS v0) ≣ var (vS (vS (vS (vS v0)))))
trans* = JJ (ext (ext c* _) _) (IdCm _) (var (vS v0) ≣ var (vS (vS (vS (vS v0)))))


-- • , var (vS (vS (vS v0))) , var (vS v0) , var v0 -- JJ {Δ = ε , * , * , (var v0 ≣ var (vS v0))} (ext c* v0) ( • , var (vS (vS (vS v0))) , var (vS v0) , var v0)  (var (vS v0) ≣ {!var (vS v0)!}) -- (var (vS v0) ≣ var (vS (vS v0))) 
-- home * y z

-- tm-reflA : 

cm+refl : (ε , *) ⇒ (ε , * , var v0 ≣ var v0)
cm+refl = IdCm _ , refl*

-- a : * , b : * , x : b ≡ a ⊢ refl x : x ≡ x

refl*ab : Tm {ε , * ,  * , var v0 ≣ var (vS v0)} (var v0  ≣ var v0) 
refl*ab = JJ (ext c* v0) (IdCm _) (var v0 ≣ var v0)

--  JJ c* (• , (var v0)) (var v0 ≣ var v0)


-- another version which could be mor useful

cm-ind :  (Γ : Con)(A : Ty Γ)(a b : Tm A) → (Γ , a ≣ b , (a +tm (a ≣ b)) ≣ (b +tm (a ≣ b)) , var v0 ≣ var (vS v0)) ⇒ (Γ , A , A +T A , var v0 ≣ var (vS v0))
cm-ind Γ * a b = {!!} -- (({!!} , a) , {!!}) , {!!}
cm-ind Γ (a ≣ b) a₁ b₁ = {!!}


refl*ind2 : {Γ : Con}(A : Ty Γ) → Tm {Γ , A , A +T A , var v0 ≣ var (vS v0)} (var v0 ≣ var v0)
refl*ind2 * = refl*ab [ ((• , (var (vS (vS v0)))) , (var (vS v0))) , (var v0) ]tm
refl*ind2 (_≣_ {A} a b) = (refl*ind2 A) [ {!!} ]tm ⟦ {!!} ⟫ -- ⇢ tm-refl A

count-ty-lv : {Γ : Con}(A : Ty Γ)  → ℕ
count-ty-lv * = 0
count-ty-lv (_≣_ {A} a b) = suc (count-ty-lv A)

-- for inductive case of contractible contexts

refl*ind : (Γ : Con)(p : isContr Γ)(A : Ty Γ)(x : Var A) → Tm {Γ ,  A , var v0 ≣ var (vS x {A})} (var v0 ≣ var v0)
refl*ind ε p A ()
refl*ind (Γ , B) p A x = JJ (ext p x) (IdCm _) (var v0 ≣ var v0) ⟦ lemIC _ ⟫

record specialCon : Set where
  constructor _,,_,,_
  field
    Δ' : Con
    A' : Ty Δ'
    P' : Ty (Δ' , A')
open specialCon

recoverCon : specialCon → Con
recoverCon (Δ' ,, A' ,, B') = (Δ' , A') , B'

makeCon :  ℕ → specialCon
makeCon 0 = (ε , *) ,, * ,, (var v0 ≣ var (vS v0))
makeCon (suc n) = let Δ = makeCon n in recoverCon Δ ,, P' Δ +T P' Δ  ,, (var v0 ≣ var (vS v0))

specialConContr : ∀{Γ}(A : Ty Γ) → isContr (recoverCon (makeCon (count-ty-lv A)))
specialConContr * = ext c* v0
specialConContr (_≣_ {A} a b) = ext (specialConContr A) v0

tm-refl :  {Γ : Con} (A : Ty Γ) → Tm {Γ , A} (var v0 ≣ var v0)
tm-refl * = refl* [ • , var v0 ]tm -- Γ , x : * ⊢ refl* (t =  x : Γ , * ⇒ *)
tm-refl {Γ} (_≣_ {A} a b) = let (Δ' ,, A' ,, P') = makeCon (count-ty-lv {Γ} A) in refl*ind (Δ' , A' , P') (specialConContr {Γ} A) (P' +T P')  {!(vS (vS v0))!} [ ((({!!} , {!b +tm ?!}) , {!!}) , {!!}) , {!!} ]tm ⟦ {!!} ⟫


{-
tm-refl {Γ} (_≣_ {*} a b) = ((refl*ind (recoverCon (makeCon (count-ty-lv {Γ} *))) (specialConContr {Γ} *) *) (vS (vS v0)) ) [ ((((• , (b +tm (a ≣ b))) , a +tm (a ≣ b)) , var v0) , a +tm (a ≣ b)) , var v0 ]tm -- (tm-refl *) [ {!!} ]tm  ⟦ {!!} ⟫ -- refl*ab [ (• , b +tm (a ≣ b)) , a +tm (a ≣ b) , var v0 ]tm


  
tm-refl (_≣_ {a ≣ b} a₁ b₁) = {!!}
-}
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

xxx : Tm {ε , * , * , (var v0 ≣ var (vS v0))} (var (vS v0) ≣ var (vS (vS v0)))
xxx = var v0 


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