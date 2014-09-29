
\AgdaHide{
\begin{code}
{-# OPTIONS --type-in-type --no-positivity-check --no-termination-check #-}


module BasicSyntax where 


open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product renaming (_,_ to _,,_)


infix 4 _≅_
infix 4 _=h_
infixl 6 _+T_ _+S_ _+tm_
infixl 5 _,_
infixl 7 _⊚_

\end{code}
}

\section{Syntax of \tig}

\begin{code}
data Con           : Set
data Ty (Γ : Con)  : Set
data Tm            : {Γ : Con}(A : Ty Γ) → Set
data Var           : {Γ : Con}(A : Ty Γ) → Set
data _⇒_           : Con → Con → Set
data isContr       : Con → Set
\end{code}

\textbf{Contexts}

\begin{code}
data Con where
  ε     : Con
  _,_   : (Γ : Con)(A : Ty Γ) → Con
\end{code}


\textbf{Types}

\begin{code}
data Ty Γ where
  *     : Ty Γ
  _=h_  : {A : Ty Γ}(a b : Tm A) → Ty Γ
\end{code}

\textbf{Heterogeneous Equality for Terms}

\begin{code}
data _≅_ {Γ : Con}{A : Ty Γ} :
         {B : Ty Γ} → Tm A → Tm B → Set where
  refl : (b : Tm A) → b ≅ b

_-¹          : ∀{Γ : Con}{A B : Ty Γ}
               {a : Tm A}{b : Tm B} → a ≅ b → b ≅ a
(refl _) -¹  = refl _

infixr 4 _∾_ 

_∾_ : {Γ : Con}
      {A B C : Ty Γ}
      {a : Tm A}{b : Tm B}{c : Tm C} →
      a ≅ b → 
      b ≅ c 
    → a ≅ c
_∾_ {c = c} (refl .c) (refl .c) = refl c

_⟦_⟫        : {Γ : Con}{A B : Ty Γ}(a : Tm B) 
            → A ≡ B → Tm A
a ⟦ refl ⟫  = a

cohOp       : {Γ : Con}{A B : Ty Γ}{a : Tm B}(p : A ≡ B) 
            → a ⟦ p ⟫ ≅ a
cohOp refl  = refl _
\end{code}

\begin{code}
cohOp-eq : {Γ : Con}{A B : Ty Γ}{a b : Tm B}
           {p : A ≡ B} → (a ≅ b) 
         → (a ⟦ p ⟫ ≅ b ⟦ p ⟫)
cohOp-eq {Γ} {.B} {B} {a} {b} {refl} r = r

cohOp-hom : {Γ : Con}{A B : Ty Γ}{a b : Tm B}(p : A ≡ B) →
            (a ⟦ p ⟫ =h b ⟦ p ⟫) ≡ (a =h b)
cohOp-hom refl = refl

cong≅ : {Γ Δ : Con}{A B : Ty Γ}{a : Tm A}{b : Tm B}
        {D : Ty Γ → Ty Δ} → (f : {C : Ty Γ} → Tm C → Tm (D C))→ 
        a ≅ b  → f a ≅ f b
cong≅ f (refl _) = refl _
\end{code}

\textbf{Substitutions}

\begin{code}
_[_]T   : ∀{Γ Δ} → Ty Δ → Γ ⇒ Δ → Ty Γ
_[_]V   : ∀{Γ Δ A} → Var A → (δ : Γ ⇒ Δ) → Tm (A [ δ ]T)
_[_]tm  : ∀{Γ Δ A} → Tm A → (δ : Γ ⇒ Δ) → Tm (A [ δ ]T)    
_⊚_ : ∀{Γ Δ Θ} → Δ ⇒ Θ → (δ : Γ ⇒ Δ) → Γ ⇒ Θ   
\end{code}


\textbf{Contexts morphisms}

\begin{code}
data _⇒_ where
  •    : ∀{Γ} → Γ ⇒ ε
  _,_  : ∀{Γ Δ}(δ : Γ ⇒ Δ){A : Ty Δ}(a : Tm (A [ δ ]T))
       → Γ ⇒ (Δ , A)
\end{code}

\textbf{Weakening}

\begin{code}   
_+T_   : ∀{Γ}(A : Ty Γ)(B : Ty Γ) → Ty (Γ , B)
_+tm_  : ∀{Γ A}(a : Tm A)(B : Ty Γ) → Tm (A +T B)   
_+S_   : ∀{Γ Δ}(δ : Γ ⇒ Δ)(B : Ty Γ) → (Γ , B) ⇒ Δ   
\end{code}

\begin{code}

*        +T B = *
(a =h b) +T B = a +tm B =h b +tm B


*        [ δ ]T = * 
(a =h b) [ δ ]T = a [ δ ]tm =h b [ δ ]tm

\end{code}

\textbf{Variables and terms}

\begin{code}
data Var where
  v0 : ∀{Γ}{A : Ty Γ}              → Var (A +T A)
  vS : ∀{Γ}{A B : Ty Γ}(x : Var A) → Var (A +T B)

data Tm where
  var  : ∀{Γ}{A : Ty Γ} → Var A → Tm A
  coh  : ∀{Γ Δ} → isContr Δ → (δ : Γ ⇒ Δ) 
       → (A : Ty Δ) → Tm (A [ δ ]T)

cohOpV : {Γ : Con}{A B : Ty Γ}{x : Var A}(p : A ≡ B) →
         var (subst Var p x) ≅ var x
cohOpV {x = x} refl = refl (var x)

cohOpVs : {Γ : Con}{A B C : Ty Γ}{x : Var A}(p : A ≡ B) → 
          var (vS {B = C} (subst Var p x)) ≅ var (vS x)
cohOpVs {x = x} refl = refl (var (vS x))

coh-eq : {Γ Δ : Con}{isc : isContr Δ}{γ δ : Γ ⇒ Δ}
         {A : Ty Δ} → γ ≡ δ → coh isc γ A ≅ coh isc δ A 
coh-eq refl = refl _
\end{code}

\textbf{Contractible contexts}

\begin{code}
data isContr where
  c*   : isContr (ε , *)
  ext  : ∀{Γ} → isContr Γ → {A : Ty Γ}(x : Var A) 
       → isContr (Γ , A , (var (vS x) =h var v0))     
\end{code}

\begin{code}
hom≡ : {Γ : Con}{A A' : Ty Γ}
                {a : Tm A}{a' : Tm A'}(q : a ≅ a')
                {b : Tm A}{b' : Tm A'}(r : b ≅ b')
                → (a =h b) ≡ (a' =h b')
hom≡ {Γ} {.A'} {A'} {.a'} {a'} (refl .a') {.b'} {b'} (refl .b') = refl


S-eq : {Γ Δ : Con}{γ δ : Γ ⇒ Δ}{A : Ty Δ}
        {a : Tm (A [ γ ]T)}{a' : Tm (A [ δ ]T)} 
        → γ ≡ δ → a ≅ a' 
        → _≡_ {_} {Γ ⇒ (Δ , A)} (γ , a) (δ , a')
S-eq refl (refl _) = refl
\end{code}

\textbf{Some lemmas}

\begin{code}
[⊚]T    : ∀{Γ Δ Θ A}{θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ} 
        → A [ θ ⊚ δ ]T ≡ (A [ θ ]T)[ δ ]T  

[⊚]v    : ∀{Γ Δ Θ A}(x : Var A){θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}
        → x [ θ ⊚ δ ]V ≅ (x [ θ ]V) [ δ ]tm

[⊚]tm   : ∀{Γ Δ Θ A}(a : Tm A){θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}
        → a [ θ ⊚ δ ]tm ≅ (a [ θ ]tm) [ δ ]tm

⊚assoc  : ∀{Γ Δ Θ Ω}(γ : Θ ⇒ Ω){θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}  
        → (γ ⊚ θ) ⊚ δ ≡ γ ⊚ (θ ⊚ δ)  
\end{code}

\begin{code}
•       ⊚ δ = •
(δ , a) ⊚ δ' = (δ ⊚ δ') , a [ δ' ]tm ⟦ [⊚]T ⟫

[+S]T   : ∀{Γ Δ A B}{δ : Γ ⇒ Δ}
        → A [ δ +S B ]T ≡ (A [ δ ]T) +T B 

[+S]tm  : ∀{Γ Δ A B}(a : Tm A){δ : Γ ⇒ Δ}
        → a [ δ +S B ]tm ≅ (a [ δ ]tm) +tm B

[+S]S   : ∀{Γ Δ Θ B}{δ : Δ ⇒ Θ}{γ : Γ ⇒ Δ}
        → δ ⊚ (γ +S B) ≡ (δ ⊚ γ) +S B

wk-tm+      : {Γ Δ : Con}{A : Ty Δ}{δ : Γ ⇒ Δ}(B : Ty Γ) 
            → Tm (A [ δ ]T +T B) → Tm (A [ δ +S B ]T)
wk-tm+ B t  = t ⟦ [+S]T ⟫

•       +S B = •
(δ , a) +S B = (δ +S B) , wk-tm+ B (a +tm B)

[+S]T {A = *}     = refl
[+S]T {A = a =h b} = hom≡ ([+S]tm a) ([+S]tm b)

+T[,]T    : ∀{Γ Δ A B}{δ : Γ ⇒ Δ}{b : Tm (B [ δ ]T)} 
          → (A +T B) [ δ , b ]T ≡ A [ δ ]T

+tm[,]tm  : ∀{Γ Δ A B}{δ : Γ ⇒ Δ}{c : Tm (B [ δ ]T)}
          → (a : Tm A) 
          → (a +tm B) [ δ , c ]tm ≅ a [ δ ]tm 

(var x)     +tm B = var (vS x)
(coh cΔ δ A) +tm B = coh cΔ (δ +S B) A ⟦ sym [+S]T ⟫ 

cong+tm : {Γ : Con}{A B C : Ty Γ}{a : Tm A}{b : Tm B} → 
          a ≅ b
        → a +tm C ≅ b +tm C
cong+tm (refl _) = refl _

cong+tm2 : {Γ : Con}{A B C : Ty Γ}
           {a : Tm B}(p : A ≡ B) 
         → a +tm C ≅ a ⟦ p ⟫ +tm C
cong+tm2 refl = refl _

wk-T : {Δ : Con}
       {A B C : Ty Δ}
       → A ≡ B → A +T C ≡ B +T C
wk-T refl = refl

wk-tm : {Γ Δ : Con}
         {A : Ty Δ}{δ : Γ ⇒ Δ}
         {B : Ty Δ}{b : Tm (B [ δ ]T)}  
         → Tm (A [ δ ]T) → Tm ((A +T B) [ δ , b ]T)
wk-tm t = t ⟦ +T[,]T ⟫

v0   [ δ , a ]V = wk-tm a
vS x [ δ , a ]V = wk-tm (x [ δ ]V)

wk-coh : {Γ Δ : Con}
         {A : Ty Δ}{δ : Γ ⇒ Δ}
         {B : Ty Δ}{b : Tm (B [ δ ]T)}  
         {t : Tm (A [ δ ]T)} 
         → wk-tm {B = B} {b = b} t ≅ t
wk-coh = cohOp +T[,]T

wk-coh+ : {Γ Δ : Con}
         {A : Ty Δ}{δ : Γ ⇒ Δ}
         {B : Ty Γ} 
         {x : Tm (A [ δ ]T +T B)}
          → wk-tm+ B x ≅ x
wk-coh+ = cohOp [+S]T

wk-hom : {Γ Δ : Con}
         {A : Ty Δ}{δ : Γ ⇒ Δ}
         {B : Ty Δ}{b : Tm (B [ δ ]T)}  
         {x y : Tm (A [ δ ]T)}
         → (wk-tm {B = B} {b = b} x =h wk-tm 
         {B = B} {b = b} y) ≡ (x =h y)
wk-hom = hom≡ wk-coh wk-coh


wk-hom+ : {Γ Δ : Con}
         {A : Ty Δ}{δ : Γ ⇒ Δ}
         {B : Ty Γ} 
         {x y : Tm (A [ δ ]T +T B)}
         → (wk-tm+ B x =h wk-tm+ B y) ≡ (x =h y)
wk-hom+ = hom≡ wk-coh+ wk-coh+


wk-⊚ : {Γ Δ Θ : Con}
       {θ : Δ ⇒ Θ}{δ : Γ ⇒ Δ}{A : Ty Θ}
       → Tm ((A [ θ ]T)[ δ ]T) → Tm (A [ θ ⊚ δ ]T)
wk-⊚ t = t ⟦ [⊚]T ⟫

[+S]S {δ = •} = refl
[+S]S {δ = δ , a} = S-eq [+S]S (cohOp [⊚]T ∾ 
      ([+S]tm a ∾ cong+tm2 [⊚]T) ∾ wk-coh+ -¹)


wk+S+T : ∀{Γ Δ : Con}{A : Ty Γ}{B : Ty Δ}
          {γ}{C} → 
          A [ γ ]T ≡ C 
       → A [ γ +S B ]T ≡ C +T B
wk+S+T eq = trans [+S]T (wk-T eq)

wk+S+tm : {Γ Δ : Con}{A : Ty Γ}{B : Ty Δ}
          (a : Tm A){C : Ty Δ}{γ : Δ ⇒ Γ}{c : Tm C} →
          a [ γ ]tm ≅ c 
        → a [ γ +S B ]tm ≅ c +tm B
wk+S+tm _ eq = [+S]tm _ ∾ cong+tm eq


wk+S+S : ∀{Γ Δ Δ₁ : Con}{δ : Δ ⇒ Δ₁}{γ : Γ ⇒ Δ}
         {ω : Γ ⇒ Δ₁}{B : Ty Γ}
       → δ ⊚ γ ≡ ω
       → δ ⊚ (γ +S B) ≡ ω +S B
wk+S+S eq = trans [+S]S (cong (λ x → x +S _) eq)


[⊚]T {A = *} = refl
[⊚]T {A = _=h_ {A} a b} = hom≡ ([⊚]tm _) ([⊚]tm _) 

+T[,]T {A = *} = refl
+T[,]T {A = _=h_ {A} a b} = hom≡  (+tm[,]tm _) (+tm[,]tm _)

var x       [ δ ]tm = x [ δ ]V
coh cΔ γ A  [ δ ]tm = coh cΔ (γ ⊚ δ) A ⟦ sym [⊚]T ⟫
\end{code}

\begin{code}


congT : ∀ {Γ Δ : Con}{A B : Ty Δ}{γ : Γ ⇒ Δ} → A ≡ B → A [ γ ]T ≡ B [ γ ]T 
congT refl = refl

congT2 : ∀ {Γ Δ} → {δ γ : Δ ⇒ Γ}{A : Ty Γ} → δ ≡ γ → A [ δ ]T ≡ A [ γ ]T
congT2 refl = refl 

congV : {Γ Δ : Con}{A B : Ty Δ}{a : Var A}{b : Var B} →
     var a ≅ var b → 
     {δ : Γ ⇒ Δ} 
     → a [ δ ]V ≅ b [ δ ]V
congV {Γ} {Δ} {.B} {B} {.b} {b} (refl .(var b)) = refl _

congtm : {Γ Δ : Con}{A B : Ty Γ}{a : Tm A}{b : Tm B}
      (p : a ≅ b) → 
      {δ : Δ ⇒ Γ}
      → a [ δ ]tm ≅ b [ δ ]tm
congtm (refl _) = refl _ 

congtm2 : {Γ Δ : Con}{A : Ty Γ}{a : Tm A}
          {δ γ : Δ ⇒ Γ} →
          (p : δ ≡ γ)
        → a [ δ ]tm ≅ a [ γ ]tm
congtm2 refl = refl _

⊚assoc • = refl
⊚assoc (_,_ γ {A} a) = S-eq (⊚assoc γ) 
    (cohOp [⊚]T 
    ∾ (congtm (cohOp [⊚]T)
    ∾ ((cohOp [⊚]T 
    ∾ [⊚]tm a) -¹)))


[⊚]v (v0 {Γ₁} {A}) {θ , a}  = wk-coh ∾ cohOp 
  [⊚]T ∾ congtm (cohOp +T[,]T -¹) 
[⊚]v (vS {Γ₁} {A} {B} x) {θ , a} = 
  wk-coh ∾ ([⊚]v x ∾ (congtm (cohOp +T[,]T) -¹))



[⊚]tm (var x) = [⊚]v x
[⊚]tm (coh c γ A) = cohOp (sym [⊚]T) ∾ (coh-eq (sym (⊚assoc γ))
           ∾ cohOp (sym [⊚]T) -¹) ∾ congtm (cohOp (sym [⊚]T) -¹)


⊚wk : ∀{Γ Δ Δ₁}{B : Ty Δ}(γ : Δ ⇒ Δ₁){δ : Γ ⇒ Δ}
      {c : Tm (B [ δ ]T)} → (γ +S B) ⊚ (δ , c) ≡ γ ⊚ δ
⊚wk • = refl
⊚wk (_,_ γ {A} a) = S-eq (⊚wk γ) (cohOp [⊚]T ∾
    (congtm (cohOp [+S]T) ∾ +tm[,]tm a) ∾ cohOp [⊚]T -¹)

+tm[,]tm (var x) = cohOp +T[,]T
+tm[,]tm (coh x γ A) = congtm (cohOp (sym [+S]T)) ∾ 
   cohOp (sym [⊚]T) ∾ coh-eq (⊚wk γ) ∾ cohOp (sym [⊚]T) -¹



[+S]V : {Γ Δ : Con}{A : Ty Δ}
         (x : Var A){δ : Γ ⇒ Δ}
         {B : Ty Γ}
         → x [ δ +S B ]V ≅ (x [ δ ]V) +tm B
[+S]V v0 {_,_ δ {A} a} = wk-coh ∾ wk-coh+ ∾ cong+tm2 +T[,]T
[+S]V (vS x) {δ , a} = wk-coh ∾ [+S]V x ∾ cong+tm2 +T[,]T


[+S]tm (var x) = [+S]V x
[+S]tm (coh x δ A) = cohOp (sym [⊚]T) ∾ coh-eq [+S]S ∾ 
  cohOp (sym [+S]T) -¹ ∾ cong+tm2 (sym [⊚]T)
\end{code}

\textbf{Some simple contexts}

\begin{code}
x:* : Con
x:* = ε , *

x:*,y:*,α:x=y : Con
x:*,y:*,α:x=y = x:* , * , (var (vS v0) =h var v0)

vX : Tm {x:*,y:*,α:x=y} *
vX = var (vS (vS v0))

vY : Tm {x:*,y:*,α:x=y} *
vY = var (vS v0)

vα : Tm {x:*,y:*,α:x=y} (vX =h vY)
vα = var v0

x:*,y:*,α:x=y,z:*,β:y=z : Con
x:*,y:*,α:x=y,z:*,β:y=z = x:*,y:*,α:x=y , * , 
  (var (vS (vS v0)) =h var v0)

vZ : Tm {x:*,y:*,α:x=y,z:*,β:y=z} *
vZ = var (vS v0)

vβ : Tm {x:*,y:*,α:x=y,z:*,β:y=z} (vY +tm _ +tm _ =h vZ)
vβ = var v0
\end{code}

