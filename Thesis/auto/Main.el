(TeX-add-style-hook "Main"
 (lambda ()
    (LaTeX-add-bibliographies
     "my")
    (LaTeX-add-labels
     "Bibliography")
    (TeX-add-symbols
     "HRule")
    (TeX-run-style-hooks
     "tikz"
     "mypack"
     "fixme"
     "xkvltxp"
     "natbib"
     "square"
     "numbers"
     "comma"
     "sort&compress"
     "diagxy"
     "proof"
     "booktabs"
     "xspace"
     "inputenc"
     "utf8x"
     "textgreek"
     "stmaryrd"
     "autofe"
     "amssymb"
     "amsfonts"
     "amsmath"
     "color"
     "relsize"
     "amsthm"
     "dsfont"
     "agda"
     "xy"
     "all"
     "etex"
     "latex2e"
     "Thesis11"
     "Thesis"
     "11pt"
     "a4paper"
     "UKenglish"
     "twoside"
     "openright"
     "macros"
     "Chapters/Introduction"
     "Chapters/Background"
     "Chapters/QuotientTypes"
     "Chapters/DefinableQuotients"
     "Chapters/Reals"
     "Chapters/SetoidModel"
     "Chapters/HITs"
     "Chapters/OGModel"
     "Chapters/Summary"
     "Appendices/AppendixA")))

