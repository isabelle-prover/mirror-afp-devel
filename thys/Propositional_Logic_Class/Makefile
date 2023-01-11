.PHONY: all dutchbook clean

THEORY_FILES = $(shell find . -type f -name '*.thy')

all: dutchbook

dutchbook: output/document.pdf

output/document.pdf: ROOT $(THEORY_FILES) document/root.tex document/root.bib
	isabelle build -c -v -d . Class_Propositional_Logic

clean:
	rm -rf output
