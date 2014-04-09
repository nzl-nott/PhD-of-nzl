(TeX-add-style-hook "OGModel"
 (lambda ()
    (LaTeX-add-labels
     "wog"
     "sec:syntax")
    (TeX-run-style-hooks
     "Chapters/OGModel/BasicSyntax2"
     "Chapters/OGModel/Suspension"
     "Chapters/OGModel/BasicLaws"
     "Chapters/OGModel/GroupoidLaws"
     "Chapters/OGModel/Telescopes"
     "Chapters/OGModel/GlobularSets"
     "Chapters/OGModel/Semantics")))

