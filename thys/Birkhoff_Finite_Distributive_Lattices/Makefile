.PHONY: all clean

THEORY_FILES = $(shell find . -type f -name '*.thy')

all: output/document.pdf

output/document.pdf: ROOT $(THEORY_FILES) document/root.tex document/root.bib
	isabelle build -c -v -d . Birkhoff_Finite_Distributive_Lattices

clean:
	rm -rf output
