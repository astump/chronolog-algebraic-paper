main.pdf: main.tex Makefile definitions.tex paper.bib
	rm -f *.aux
	pdflatex -shell-escape main
	bibtex main
	pdflatex -shell-escape main
	pdflatex -shell-escape main

clean:
	rm -f *.aux *.log *.pyg *.out *.bbl *.blg main.pdf
