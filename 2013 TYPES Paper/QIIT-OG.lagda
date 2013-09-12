
\AgdaHide{
\begin{code}
module QIIT-OG where




data Con           : Set
data Ty (Γ : Con)  : Set
data Tm            : {Γ : Con}(A : Ty Γ) → Set
data Var           : {Γ : Con}(A : Ty Γ) → Set
data _⇒_           : Con → Con → Set

data isContr       : Con → Set

~Con : Con → Con → Set -- should be Prop
~Ty : {Γ Δ : Con}{p : Γ ~Con Δ} → Ty Γ → Ty Δ → Set
~Tm : {Γ Δ : Con}{p : Γ ~Con Δ} → (A : Ty Γ)(B : Ty Δ)(A ~Ty B) → Tm A → Tm B → Set
~⇒ : (Γ Δ : Con)(p : Γ ~Con Δ)(Γ' Δ' : Con)(p' : Γ' ~Con Δ') → Γ ⇒ Γ' → Δ ⇒ Δ' → Set

transportC : {Γ Δ : Con}{p : Γ ~Con Δ}(P : Con → Set) → P Γ → P Δ

transportTy : 

data Con where
  ε   : Con
  _,_ : (Γ : Con)(A : Ty Γ) → Con


data Ty Γ where
  *    : Ty Γ
  _=h_ : {A : Ty Γ}(a b : Tm A) → Ty Γ




_[_]T  : {Γ Δ : Con}(A : Ty Δ)           (δ : Γ ⇒ Δ) → Ty Γ
_[_]V  : {Γ Δ : Con}{A : Ty Δ}(a : Var A)(δ : Γ ⇒ Δ) → Tm (A [ δ ]T)
_[_]tm : {Γ Δ : Con}{A : Ty Δ}(a : Tm A) (δ : Γ ⇒ Δ) → Tm (A [ δ ]T)
_⊚_    : {Γ Δ Θ : Con}      →  Δ ⇒ Θ → (δ : Γ ⇒ Δ) → Γ ⇒ Θ



_+T_  : {Γ : Con}(A : Ty Γ)           → (B : Ty Γ) → Ty (Γ , B)
_+tm_ : {Γ : Con}{A : Ty Γ}(a : Tm A) → (B : Ty Γ) → Tm (A +T B)
_+S_  : {Γ : Con}{Δ : Con}(δ : Γ ⇒ Δ) → (B : Ty Γ) → (Γ , B) ⇒ Δ

data Var where
  v0 : {Γ : Con}{A : Ty Γ}              → Var (A +T A)
  vS : {Γ : Con}{A B : Ty Γ}(x : Var A) → Var (A +T B)

data Tm where
  var : {Γ : Con}{A : Ty Γ} → Var A → Tm A
  JJ  : {Γ Δ : Con} → isContr Δ → (δ : Γ ⇒ Δ) → (A : Ty Δ) 


data isContr where
  c*  : isContr (ε , *)
  ext : {Γ : Con} 
      → isContr Γ → {A : Ty Γ}(x : Var A) 
        → isContr ((Γ , A) , (var (vS x) =h var v0))
      → Tm (A [ δ ]T)



data _⇒_ where
  •    : {Γ : Con} → Γ ⇒ ε
  _,_ : {Γ Δ : Con}(δ : Γ ⇒ Δ){A : Ty Δ}(a : Tm (A [ δ ]T)) 
      → Γ ⇒ (Δ , A)

\end{code}
\