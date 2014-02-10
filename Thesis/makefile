# Generic make file for LaTeX: requires GNU make

TEXFILE	= Main.tex
BIBFILE = my.bib

#Generally all targets in your Makefile which do not produce an output file with the same name as the target name should be PHONY. This typically includes all, install, clean, distclean, and so on.

.PHONY	: all show clean redo

all : pdf

pdf : $(TEXFILE:.tex=.pdf)

%.aux : %.tex
	pdflatex $< 

%.bbl : %.aux
	bibtex $<

%.pdf : %.bbl
	pdflatex $(<:.bbl=.tex)
	pdflatex $(<:.bbl=.tex)
#egrep -i "(Reference|Citation).*undefined" $(<:%.bbl=%.log)  2>&1 > /dev/null
clean	:
	  @rm -f \
	$(TEXFILE:.tex=.aux) \
	$(TEXFILE:.tex=.log) \
	$(TEXFILE:.tex=.out) \
	$(TEXFILE:.tex=.pdf) \
	$(TEXFILE:.tex=.blg) \
	$(TEXFILE:.tex=.ptb) \
	$(TEXFILE:.tex=.toc) \
	$(TEXFILE:.tex=.bbl)


one : $(TEXFILE)
	pdflatex $<

show : 
	open $(TEXFILE:.tex=.pdf)