#!/bin/bash

for f in ./*.lagda; do 
   agda --latex --include-path="/Users/txa/Agda/lib/src" --include-path="." ${f%.lagda}.lagda 
done

cd latex

pdflatex AIOOG.tex

bibtex AIOOG.aux

pdflatex AIOOG.tex

pdflatex AIOOG.tex


