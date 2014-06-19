(TeX-add-style-hook "BasicSyntax"
 (lambda ()
    (LaTeX-add-bibliographies
     "latex/my.bib")
    (LaTeX-add-labels
     "Agda"
     "sec:syntax"
     "sec:het"
     "sec:susp-and-repl"
     "sec:susp"
     "sec:replacement")
    (TeX-add-symbols
     '("oxr" 1)
     '("txa" 1)
     "mycrnotice"
     "myconfname"
     "Tm"
     "Ty"
     "doi"
     "crnotice"
     "confname")
    (TeX-run-style-hooks
     "extdash"
     "shortcuts"
     "footmisc"
     "stable"
     "url"
     "mypack"
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
     "dsfont"
     "agda"
     "latex2e"
     "sig-alternate10"
     "sig-alternate")))

