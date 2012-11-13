(TeX-add-style-hook "Report"
 (lambda ()
    (LaTeX-add-bibliographies
     "quotients")
    (LaTeX-add-environments
     "definition"
     "codes")
    (LaTeX-add-labels
     "sec:bg"
     "tt"
     "sec:lr"
     "sec:ob"
     "sec:rd"
     "sec:definitions"
     "sec:cl")
    (TeX-add-symbols
     '("dlift" 1)
     '("class" 1)
     '("ed" 1)
     '("todo" 1)
     "N"
     "Q"
     "R"
     "Z"
     "dotph"
     "dotop"
     "abs"
     "norm"
     "set"
     "eqqm"
     "sep"
     "itt"
     "ett"
     "mltt"
     "textmu")
    (TeX-run-style-hooks
     "varioref"
     "url"
     "autofe"
     "amssymb"
     "amsfonts"
     "amsmath"
     "color"
     "amsthm"
     "dsfont"
     "latex2e"
     "art10"
     "article")))

