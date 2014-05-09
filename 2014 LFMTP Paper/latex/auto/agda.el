(TeX-add-style-hook "agda"
 (lambda ()
    (LaTeX-add-environments
     "code")
    (TeX-add-symbols
     '("AgdaIndent" 1)
     '("AgdaHole" 1)
     '("AgdaTerminationProblem" 1)
     '("AgdaPrimitive" 1)
     '("AgdaPostulate" 1)
     '("AgdaCoinductiveConstructor" 1)
     '("AgdaInductiveConstructor" 1)
     '("AgdaPrimitiveType" 1)
     '("AgdaBoundFontStyle" 1)
     '("AgdaCommentFontStyle" 1)
     '("AgdaStringFontStyle" 1)
     '("AgdaFontStyle" 1)
     "AgdaComment"
     "AgdaKeyword"
     "AgdaString"
     "AgdaNumber"
     "AgdaSymbol"
     "AgdaOperator"
     "AgdaBound"
     "AgdaDatatype"
     "AgdaField"
     "AgdaFunction"
     "AgdaModule"
     "AgdaRecord"
     "AgdaDottedPattern"
     "AgdaUnsolvedMeta"
     "AgdaIncompletePattern"
     "AgdaError"
     "AgdaCodeStyle"
     "mathindent"
     "AgdaHide")
    (TeX-run-style-hooks
     "inputenc"
     "utf8x"
     "fontenc"
     "T1"
     "tipa"
     "safe"
     "amssymb"
     "amsfonts"
     "ucs"
     "unicode-math"
     "fontspec"
     "polyglossia"
     "polytable"
     "xcolor"
     "ifxetex")))

