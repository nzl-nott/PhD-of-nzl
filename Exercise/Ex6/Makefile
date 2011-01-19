# a.bbl b.aux c.tex d.pdf a = b , b = c , d = c

%.tex : %.lagda
	lhs2TeX --agda $< -o $@

%.aux : %.tex
	latex $<

%.bbl : %.aux %.tex
	bibtex $<

%.pdf : %.tex %.bbl
	latex $<
	pdflatex $<

clean:
	rm *.toc *.aux *.pdf *.ps *.eps *.log *.lof *.bbl *.blg *.dvi
