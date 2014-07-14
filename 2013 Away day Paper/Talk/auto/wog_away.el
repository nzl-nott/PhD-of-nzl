(TeX-add-style-hook "wog_away"
 (lambda ()
    (LaTeX-add-environments
     '("colorblock" 2))
    (TeX-add-symbols
     '("judgeType" 1)
     '("judgeTerm" 2)
     '("refl" 1)
     '("ruleTermE" 2)
     '("ruleTypeE" 1)
     '("ruleTerm" 3)
     '("ruleType" 2)
     "type"
     "set"
     "wig"
     "mltt"
     "og"
     "wog"
     "hott"
     "ott"
     "tig")
    (TeX-run-style-hooks
     "semantic"
     "inference"
     "fancybox"
     "cmbright"
     "fontenc"
     "T1"
     "textpos"
     "absolute"
     "overlay"
     "quiet"
     "apacite"
     "nobibnewpage"
     "notocbib"
     "booktabs"
     "xy"
     "all"
     "animate"
     "multimedia"
     "graphicx"
     "babel"
     "english"
     "stmaryrd"
     "amssymb"
     "amsmath"
     "ifthen"
     "xspace"
     "textgreek"
     "autofe"
     "relsize"
     "inputenc"
     "utf8x"
     "ucs"
     "agda"
     "etex"
     "latex2e"
     "beamer12"
     "beamer"
     "12pt"
     "mathserif"
     "handout")))

