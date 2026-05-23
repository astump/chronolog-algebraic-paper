abstract.pdf: abstract.tex Makefile definitions.tex paper.bib
	rm -f *.aux
	pdflatex -shell-escape abstract
	bibtex abstract
	pdflatex -shell-escape abstract
	pdflatex -shell-escape abstract

clean:
	rm -f *.aux *.log *.pyg *.out *.bbl *.blg
