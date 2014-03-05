(TeX-add-style-hook "SetoidModel"
 (lambda ()
    (LaTeX-add-labels
     "sm")
    (TeX-run-style-hooks
     "./CwF/latex/hProp"
     "./CwF/Cats/latex/Category"
     "./CwF/latex/CategoryOfSetoid"
     "./CwF/latex/CwF-setoid"
     "./CwF/latex/CwF-ctd"
     "./CwF/latex/CwF-quotient")))

