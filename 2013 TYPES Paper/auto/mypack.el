(TeX-add-style-hook "mypack"
 (lambda ()
    (LaTeX-add-environments
     "theorem"
     "lemma"
     "proposition"
     "corollary")
    (TeX-add-symbols
     '("bigslant" 2)
     '("ed" 1)
     '("todo" 1)
     "N"
     "Q"
     "R"
     "Z"
     "C"
     "itt"
     "ett"
     "mltt")))

