ifeq ($(AGDA_LIB),)
	AGDA_LIB=~/Agda/lib/src
endif

DEPS = latex/IdentityContextMorphisms.tex latex/GlobularTypes.tex latex/GroupoidStructure.tex latex/Suspension.tex latex/BasicSyntax.tex latex/BasicSyntax.bbl latex/Semantics.tex latex/Telescopes2.tex

all : pdf

latex/%.tex : %.lagda
	agda $(AGDA_ARGS) --latex  -i . -i $(AGDA_LIB) $<

latex/BasicSyntax.aux : $(DEPS)
	cd latex ; pdflatex BasicSyntax.tex ;	cd .. 

latex/BasicSyntax.bbl : latex/my.bib latex/BasicSyntax.aux
	bibtex latex/BasicSyntax

pdf : $(DEPS)
	cd latex ; pdflatex BasicSyntax.tex ;	pdflatex BasicSyntax.tex ; cd .. 


clean :
	rm -f latex/*.{aux,bbl,blg,log,out,ptb,ptbx,vtc}