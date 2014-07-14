(TeX-add-style-hook "DefinableQuotients"
 (lambda ()
    (LaTeX-add-bibliographies
     "my")
    (LaTeX-add-environments
     "definition"
     "remark")
    (LaTeX-add-labels
     "sec:related-work"
     "enum:Q"
     "enum:box"
     "enum:sound"
     "enum:elim"
     "def:coequalizer")
    (TeX-run-style-hooks
     "mypack"
     "xypic"
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
     "agda"
     "latex2e"
     "art10"
     "article"
     "Quotient")))

