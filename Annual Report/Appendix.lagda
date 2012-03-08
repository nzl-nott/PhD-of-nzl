
\newpage

\oddsidemargin=-1cm
\evensidemargin=-1cm
\begin{appendix}

\section{Appendix}

\begin{code}

sound                      : ∀ {x y} → x ∼ y → [ x ] ≡ [ y ]
sound { x } { y } x∼y = ⌞ compl >∼< x∼y >∼< compl' ⌟ 

\end{code}


\begin{code}

compl                            : ∀ {n} → ⌜ [ n ] ⌝ ∼ n
compl {x , 0}                 = refl
compl {0 , nsuc y}         = refl
compl {nsuc x , nsuc y} = compl {x , y} >∼<  ⟨ sm+n≡m+sn x y ⟩

\end{code}


\begin{code}

stable                : ∀ {n} → [ ⌜ n ⌝ ] ≡ n
stable {+ n}       = refl
stable { -suc n } = refl

\end{code}


\begin{code}

dis2ˡ : ∀ a b c d e f → a * (b + c) + d * (e + f) ≡ (a * b + a * c) + (d * e + d * f) 
dis2ˡ a b c d e f = distˡ a b c += distˡ d e f

ex :  ∀ a b c → a + (b + c) ≡ b + (a + c)
ex a b c = ⟨ +-assoc a b c ⟩ >≡< +-comm a b ⋆+ c >≡< +-assoc b a c

exchange₃ : ∀ m n p q → (m + n) + (p + q) ≡ (m + p) + (n + q)
exchange₃ m n p q = +-assoc m n (p + q) >≡<
  m +⋆ (ex n p q) >≡<
  ⟨ +-assoc m p (n + q) ⟩

dist-lemˡ : ∀ a b c d e f → a * (c + e) + b * (d + f) ≡ (a * c + b * d) + (a * e + b * f) 
dist-lemˡ a b c d e f = dis2ˡ a c e b d f >≡< exchange₃ (a * c) (a * e) (b * d) (b * f)

distʳ : _*_ DistributesOverʳ _+_
distʳ (a , b) (c , d) (e , f) = ℕ.dist-lemʳ a b c d e f += ⟨  ℕ.dist-lemʳ b a c d e f ⟩

distʳ : _*_ DistributesOverʳ _+_
distʳ a b c = sound $ ℤ₀.*-cong (compl {⌜ b ⌝ ℤ₀+ ⌜ c ⌝}) zrefl >∼< ℤ₀.distʳ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ >∼< ℤ₀.+-cong compl' compl'

\end{code}

\begin{code}

liftOp1-β : (f : Op 1 ℤ₀) → (cong : ∀ {a b} → a ∼ b → f a ∼ f b) → 
               ∀ n → liftOp1safe f cong [ n ] ≡ [ f n ]
liftOp1-β f cong n = sound (cong compl)


liftOp2-β : (op : Op 2 ℤ₀) → (cong : ∀ {a b c d} → a ∼ b → c ∼ d → op a c ∼ op b d) →
              ∀ m n → liftOp2safe op cong [ m ] [ n ] ≡ [ op m n ] 
liftOp2-β op cong m n = sound (cong compl compl)

\end{code}

\begin{code}
liftId : ∀ {op : Op 2 ℤ₀}(e : ℤ) → Identity _∼_ ⌜ e ⌝ op → Identity e (liftOp 2 op)
liftId e (idl , idr) = (λ x → sound (idl ⌜ x ⌝) >≡< stable) , (λ x → sound (idr ⌜ x ⌝) >≡< stable)

liftAssoc : ∀ {op : Op 2 ℤ₀}(cong : Cong2 op) → Associative _∼_ op → Associative (liftOp2safe op cong)
liftAssoc {op} cong assoc a b c = sound (cong (compl {op ⌜ a ⌝ ⌜ b ⌝}) zrefl >∼< assoc ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ >∼< cong zrefl compl')

liftMonoid : {op : Op 2 ℤ₀}{e : ℤ}(cong : Cong2 op) → IsMonoid _∼_ op ⌜ e ⌝ → IsMonoid _≡_ (liftOp 2 op) e
liftMonoid {op} {e} cong im = record 
  { isSemigroup = record 
    { isEquivalence = isEquivalence
    ; assoc = liftAssoc cong (IsMonoid.assoc im)
    ; ∙-cong = cong₂ (liftOp 2 op)
    }
  ; identity = liftId {op} e (IsMonoid.identity im)
  }
\end{code}


\begin{code}

[_] : ℚ₀ → ℚ
[ (+ 0) /suc d ] = ℤ.+_ 0 ÷ 1
[ (+ (suc n)) /suc d ] with gcd (suc n) (suc d)
[ (+ suc n) /suc d ] | di , g = GCD′→ℚ (suc n) (suc d) di (λ ()) (C.gcd-gcd′ g)
[ (-suc n) /suc d ] with gcd (suc n) (suc d)
... | di , g = - GCD′→ℚ (suc n) (suc d) di (λ ()) (C.gcd-gcd′ g)

\end{code}

\begin{code}

   _Diff_on_ : Seq ℚ₀ → Seq ℚ₀ → Seq ℚ₀*
   f Diff g on m = ∣ f m - g m ∣

   _~_ : Rel ℝ₀
   (f: f p: p) ~ (f: f' p: p') =  
       ∀ (ε : ℚ₀*) → ∃ λ lb → ∀ i → (lb < i) → f Diff f' on i <' ε

\end{code}

\end{appendix}