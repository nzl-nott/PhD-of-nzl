# Generic make file for LaTeX: requires GNU make

TEXFILE	= Main.tex
BIBFILE = my.bib

#Generally all targets in your Makefile which do not produce an output file with the same name as the target name should be PHONY. This typically includes all, install, clean, distclean, and so on.

.PHONY	: all show clean

all : pdf

pdf : $(TEXFILE:.tex=.pdf)

%.aux : %.tex
	pdflatex $<  2>&1 > /dev/null

%.bbl : %.aux
	bibtex $<  2>&1 > /dev/null

%.pdf : %.bbl
	pdflatex $(<:.bbl=.tex) 2>&1 > /dev/null
	pdflatex $(<:.bbl=.tex) 2>&1 > /dev/null
	egrep -i "(Reference|Citation).*undefined" $(<:%.bbl=%.log) 

clean	:
	  @rm -f \
	$(TEXFILE:.tex=.aux) \
	$(TEXFILE:.tex=.log) \
	$(TEXFILE:.tex=.out) \
	$(BIBFILE:.bib=.bbl)


one : $(TEXFILE)
	pdflatex $<

show : 
	open $(TEXFILE:.tex=.pdf)