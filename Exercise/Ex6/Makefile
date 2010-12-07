%.tex : %.lagda
	lhs2TeX --agda $< -o $@
%.pdf : %.tex
	pdflatex $<
