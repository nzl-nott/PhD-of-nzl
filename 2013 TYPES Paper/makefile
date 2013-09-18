ifeq ($(AGDA_LIB),)
	AGDA_LIB=~/Agda/lib/src
endif

DEPS = latex/AIOOGS2.tex latex/GlobularSets.tex latex/BasicLaws.tex latex/GroupoidLaws.tex latex/Suspension.tex latex/AIOOG.tex latex/AIOOG.bbl latex/Semantics.tex

all : pdf

latex/%.tex : %.lagda
	agda --latex  -i . -i $(AGDA_LIB) $<


latex/AIOOG.aux : $(DEPS)
	cd latex ; pdflatex AIOOG.tex ;	cd .. 

latex/AIOOG.bbl : latex/my.bib latex/AIOOG.aux
	bibtex latex/AIOOG

<<<<<<< HEAD
pdf : latex/AIOOGS2.tex  latex/Semantics.tex latex/GlobularSets.tex latex/BasicLaws.tex latex/GroupoidLaws.tex  latex/Suspension.tex latex/AIOOG.tex latex/AIOOG.bbl
=======
pdf : $(DEPS)
>>>>>>> bb1363024ffccb5023b11d2390886f862aede8a1
	cd latex ; pdflatex AIOOG.tex ;	cd .. 
