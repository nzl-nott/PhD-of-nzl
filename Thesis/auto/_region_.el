(TeX-add-style-hook "_region_"
 (lambda ()
    (LaTeX-add-bibliographies
     "my.bib")
    (LaTeX-add-labels
     "Bibliography")
    (TeX-add-symbols
     "HRule")
    (TeX-run-style-hooks
     "tbib"
     "na"
     "square"
     "numbers"
     "comma"
     "sort&compress"
     "diagxy"
     "inputenc"
     "utf8x"
     "ucs"
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
     "mypack"
     "xy"
     "matrix"
     "latex2e"
     "Thesis11"
     "Thesis"
     "11pt"
     "a4paper"
     "UKenglish"
     "twoside"
     "openright"
     "Chapters/QuotientTypes")))

