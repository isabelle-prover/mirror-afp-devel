# change this to your main tex file
FILENAME = guide

all: main

main: *.tex
	pdflatex $(FILENAME).tex
	pdflatex $(FILENAME).tex

clean:
	rm -fv $(FILENAME).dvi
	rm -fv $(FILENAME).ps
	rm -fv *.aux
	rm -fv $(FILENAME).log
	rm -fv *.toc
	rm -fv *.bbl
	rm -fv *.blg
	rm -fv *.glo
	rm -fv *.out
	rm -fv *.nav
	rm -fv *.snm
	rm -fv *.log
	rm -fv *.vrb
	rm -fv *~

