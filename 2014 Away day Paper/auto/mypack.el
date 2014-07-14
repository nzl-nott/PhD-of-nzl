(TeX-add-style-hook "mypack"
 (lambda ()
    (TeX-add-symbols
     '("pullbackcorner" ["argument"] 0)
     '("dlift" 1)
     '("class" 1)
     '("ra" 1)
     '("morph" 2)
     '("qset" 1)
     '("climeta" 1)
     '("clim" 1)
     '("tometa" 1)
     '("bigslant" 2)
     "N"
     "PN"
     "Q"
     "R"
     "Z"
     "itt"
     "ett"
     "hott"
     "ott"
     "mltt"
     "wig"
     "og"
     "wog"
     "tig"
     "iscauchy"
     "infixeqv"
     "dotph"
     "dotop"
     "abs"
     "norm"
     "set"
     "defeq"
     "slash")
    (TeX-run-style-hooks
     "xspace")))

