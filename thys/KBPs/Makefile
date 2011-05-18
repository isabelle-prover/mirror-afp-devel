all: pdf

%.pdf: %.eps
	epstopdf -o $@ $<

pdf: generate
	cd generated && make pdf
	@echo generated/root.pdf

generate: scripts/funs generated/session.tex generated/root.tex

generated/root.tex: document/*.tex document/*.bib document/*.cls
	cp -rf document/* generated
	ls generated/*.tex | xargs -n 1 scripts/funny

generated/session.tex: ROOT.ML *.thy
	isabelle make
	ls generated/*.tex | xargs -n 1 scripts/funny

scripts/funs: scripts/funs.lex.sml scripts/funs.sml scripts/funs.mlb
	mlton scripts/funs.mlb

scripts/funs.lex.sml: scripts/funs.lex
	mllex scripts/funs.lex

clean:
	rm -f scripts/funs.lex.sml scripts/funs
	find . -name "*~" | xargs rm -f
	rm -rf generated
	isabelle make clean
