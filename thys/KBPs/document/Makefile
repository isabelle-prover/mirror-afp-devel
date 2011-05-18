# sub makefile, called by master in parent dir

all: pdf

pdf:
	pdflatex root
	bibtex root
	pdflatex root
	pdflatex root

clean:
	rm -f *.log *.toc *.bbl *.blg *.aux *.out
