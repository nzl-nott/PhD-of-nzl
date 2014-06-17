\AgdaHide{
\begin{code}

module GroupoidLaws where


open import Relation.Binary.PropositionalEquality 
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat


open import BasicSyntax renaming (_∾_ to htrans)
open import BasicSyntax2
open import Suspension
open import BasicLaws


\end{code}
}


For each of reflexivity, symmetry and transitivity we can construct appropriate coherence 2-cells witnessing the groupoid axioms. 
The base case for variable contexts is proved simply using contractibility. 
We use substitution to define the application of the three basic terms we have defined above.

\AgdaHide{
\begin{code}

reflX : Tm (vX =h vX)
reflX = refl-Tm * +tm _ +tm _

reflY : Tm (vY =h vY)
reflY = refl-Tm * +tm _

m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q : Con
m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q = x:*,y:*,α:x=y,z:*,β:y=z , * , (var (vS (vS v0)) =h var v0)

vM : Tm {m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q} *
vM = var (vS (vS (vS (vS (vS (vS v0))))))

vN : Tm {m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q} *
vN = var (vS (vS (vS (vS (vS v0)))))

vMN : Tm {m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q} (vM =h vN)
vMN = var (vS (vS (vS (vS v0))))

vP : Tm {m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q} *
vP = var (vS (vS (vS v0)))

vNP : Tm {m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q} (vN =h vP)
vNP = var (vS (vS v0))

vQ : Tm {m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q} *
vQ = var (vS v0)

vPQ : Tm {m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q} (vP =h vQ)
vPQ = var v0

Ty-G-assoc* : Ty m:*,n:*,α:m=n,p:*,β:n=p,q:*,γ:p=q
Ty-G-assoc* = (trans*-Tm [ ((((• , vM) , vP) , 
                       (trans*-Tm [ pr1 ⊚ pr1 ]tm)) , vQ) , vPQ ]tm =h 
             trans*-Tm [ (pr1 ⊚ pr1 ⊚ pr1 ⊚ pr1 , vQ) , 
                       (trans*-Tm [ ((((• , vN) , vP) , vNP) , vQ) , vPQ ]tm) ]tm)

\end{code}
}

\begin{code}
Tm-right-identity* : Tm {x:*,y:*,α:x=y}
         (trans*-Tm [ IdCm , vY , reflY ]tm =h vα)
Tm-right-identity* = Coh-Contr (ext c* v0)

Tm-left-identity* : Tm {x:*,y:*,α:x=y}
         (trans*-Tm [ ((IdCm ⊚ pr1 ⊚ pr1) , vX) , reflX , vY , vα ]tm =h vα)
Tm-left-identity* = Coh-Contr (ext c* v0)

Tm-right-inverse* : Tm {x:*,y:*,α:x=y}
         (trans*-Tm [ (IdCm , vX) , sym*-Tm ]tm =h reflX)
Tm-right-inverse* = Coh-Contr (ext c* v0)

Tm-left-inverse* : Tm {x:*,y:*,α:x=y}
         (trans*-Tm [ ((• , vY) , vX , sym*-Tm , vY) , vα ]tm =h reflY)
Tm-left-inverse* = Coh-Contr (ext c* v0)

Tm-G-assoc* : Tm Ty-G-assoc*
Tm-G-assoc* = Coh-Contr (ext (ext (ext c* v0) (vS v0)) (vS v0))
\end{code}

\noindent Their general versions are defined using replacement. For instance, for associativity, we define:

\begin{code}
Tm-G-assoc    : {Γ : Con}(A : Ty Γ) → Tm (rpl-T A Ty-G-assoc*)
Tm-G-assoc A  = rpl-tm A Tm-G-assoc* 
\end{code}

