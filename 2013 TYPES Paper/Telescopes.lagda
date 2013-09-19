
\begin{code}
{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check #-}

module Telescopes where

open import Relation.Binary.PropositionalEquality 
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat

open import AIOOG renaming (_∾_ to htrans)
open import AIOOGS2




-- The following span thing is not necessary for the final version as
-- we can define anything in the context (*) and then replace * by Γ ⊢ A
spanCon : {Γ : Con}(A : Ty Γ) → Con
spanTy : {Γ : Con}(A : Ty Γ) → Ty (spanCon A)
span⇒ : {Γ : Con}(A : Ty Γ) → Γ ⇒ spanCon A
lem-span⇒[]T : {Γ : Con}(A : Ty Γ) → (spanTy A)[ span⇒ A ]T ≡ A


spanCon {Γ} * = ε
spanCon {Γ} (_=h_ {A} _ _) = let ΩA = spanTy A in 
                           spanCon A , ΩA ,  ΩA +T  ΩA   

spanTy {Γ} * = *
spanTy {Γ} (_ =h _) = var (vS v0) =h var v0

spanisContr : {Γ : Con}(A : Ty Γ) → isContr (spanCon A , spanTy A)
spanisContr {Γ} * = c*
spanisContr {Γ} (_=h_ {A} _ _) = ext (spanisContr A) v0


span⇒ {Γ} * = •
span⇒ {Γ} (_=h_ {A} a b) = let prf = lem-span⇒[]T A in  
                         span⇒ A , a ⟦ prf ⟫  , wk-tm (b ⟦ prf ⟫)  

lem-span⇒[]T {Γ} * = refl
lem-span⇒[]T {Γ} (_=h_ {A} a b) = trans wk-hom (trans wk-hom (cohOp-hom (lem-span⇒[]T A))) 

lem-⟦⟫-trans : {Γ : Con}{A B C : Ty Γ}{a : Tm C}{AB : A ≡ B}{BC : B ≡ C} →  
                  a ⟦ trans AB BC ⟫ ≅ (a ⟦ BC ⟫)⟦ AB ⟫
lem-⟦⟫-trans {a = a}{AB = refl} {BC = refl} = refl  a


contrTypesInh : {Γ : Con}(hΓ : isContr Γ)(A : Ty Γ) → Tm A
contrTypesInh {Γ} hΓ A = JJ hΓ (IdCm _) A  ⟦ sym (IC-T A) ⟫


refl-tm : (Γ : Con)(A : Ty Γ)(t : Tm A) → Tm (t =h t)
refl-tm Γ A t = (contrTypesInh (spanisContr A) (var v0 =h var v0) [ span⇒ A , t ⟦ lem-span⇒[]T A ⟫ ]tm) 
                ⟦ sym (trans wk-hom (cohOp-hom (lem-span⇒[]T A)))  ⟫

-- define symmetry -- as mentioned above , a version for A = * and Γ = (*) is also possible.
symCon : {Γ : Con}{A : Ty Γ}{a b : Tm A}(f : Tm (a =h b)) → Con
symCon {Γ} {A} {a} {b} f = ((spanCon A , spanTy A) , spanTy A +T spanTy A) , (var (vS v0) =h var v0)

symConContr : {Γ : Con}{A : Ty Γ}{a b : Tm A}(f : Tm (a =h b)) → isContr (symCon f)
symConContr {Γ}{A}{a}{b} f = ext (spanisContr A) v0 

sym⇒ : {Γ : Con}{A : Ty Γ}{a b : Tm A}(f : Tm (a =h b)) → Γ ⇒ symCon f  
sym⇒ {Γ}{A}{a}{b} f = span⇒ A , 
                      a ⟦ lem-span⇒[]T A ⟫  , 
                      b ⟦ lem-span⇒[]T A ⟫ ⟦ +T[,]T ⟫ , 
                      f ⟦ cohOp-hom (lem-span⇒[]T A) ⟫ ⟦ wk-hom ⟫ ⟦ wk-hom ⟫
     
_[_,_] : ∀ {Γ} → (A : Ty Γ) → Tm A → Tm A → Ty Γ
A [ x , y ] =  x =h y

-- this is the type that flips the variables
symTy : {Γ : Con}{A : Ty Γ}{a b : Tm A}(f : Tm (a =h b)) → Ty (symCon f)
symTy {Γ}{A}{a}{b} f = var (vS v0) =h var (vS (vS v0)) 

sym-tm : {Γ : Con}{A : Ty Γ}{a b : Tm A}(f : Tm (a =h b)) → Tm (b =h a)
sym-tm {Γ} {A} {a} {b} f = (contrTypesInh (symConContr f) (var (vS v0) =h var (vS (vS v0))) [ sym⇒ f ]tm) 
                           ⟦ sym (trans wk-hom (trans wk-hom (trans wk-hom (cohOp-hom (lem-span⇒[]T A))) )) ⟫ 

-- composition
compCon : {Γ : Con}{A : Ty Γ}{a b c : Tm A}(f : Tm (a =h b))(g : Tm (b =h c)) → Con
compCon {Γ}{A}{a}{b}{c} f g = spanCon A ,  -- Γ
                                          spanTy A ,  -- a
                                          spanTy A +T _ , -- b 
                                          (var (vS v0) =h var v0),   -- f : a -> b
                                          spanTy A +T _ +T _ +T _ ,  -- c
                                          (var (vS (vS v0)) =h var v0)  -- g : b -> c
                                           

compConContr : {Γ : Con}{A : Ty Γ}{a b c : Tm A}(f : Tm (a =h b))(g : Tm (b =h c)) → isContr (compCon f g)
compConContr {Γ}{A}{a}{b}{c} f g = ext (ext (spanisContr A) v0) (vS v0) 

comp⇒ : {Γ : Con}{A : Ty Γ}{a b c : Tm A}(f : Tm (a =h b))(g : Tm (b =h c)) → Γ ⇒ compCon f g
comp⇒ {Γ}{A}{a}{b}{c} f g = span⇒ A , 
                            a ⟦ lem-span⇒[]T A ⟫ , 
                            b ⟦ lem-span⇒[]T A ⟫ ⟦ +T[,]T ⟫ ,  
                            f ⟦ cohOp-hom (lem-span⇒[]T A) ⟫ ⟦ wk-hom ⟫ ⟦ wk-hom ⟫ , 
                            c ⟦ lem-span⇒[]T A ⟫ ⟦ +T[,]T ⟫ ⟦ +T[,]T ⟫ ⟦ +T[,]T ⟫ , 
                            g ⟦ cohOp-hom (lem-span⇒[]T A) ⟫ ⟦ cohOp-hom +T[,]T ⟫ ⟦ cohOp-hom +T[,]T ⟫ ⟦ cohOp-hom +T[,]T ⟫ ⟦ cohOp-hom +T[,]T ⟫  

comp-tm : {Γ : Con}{A : Ty Γ}{a b c : Tm A}(f : Tm (a =h b))(g : Tm (b =h c)) → Tm (a =h c)
comp-tm {Γ}{A}{a}{b}{c} f g = (contrTypesInh (compConContr f g) (var (vS (vS (vS (vS v0)))) =h var (vS v0)) [ comp⇒ f g ]tm ) ⟦ sym (trans wk-hom (trans wk-hom (trans wk-hom (trans wk-hom (trans wk-hom (cohOp-hom (lem-span⇒[]T A))))))) ⟫ 

-- replacing composition




\end{code}

