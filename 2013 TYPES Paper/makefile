ifeq ($(AGDA_LIB),)
	AGDA_LIB=~/Agda/lib/src
endif

all : pdf

latex/%.tex : %.lagda
	agda --latex  -i . -i $(AGDA_LIB) $<

latex/my.bbl : latex/my.bib latex/AIOOG.aux
	bibtex latex/AIOOG

pdf : latex/AIOOGS2.tex latex/GlobularSets.tex latex/BasicLaws.tex latex/GroupoidLaws.tex  latex/Suspension.tex latex/AIOOG.tex latex/AIOOG.bbl
	cd latex ; pdflatex AIOOG.tex ;	cd .. 
