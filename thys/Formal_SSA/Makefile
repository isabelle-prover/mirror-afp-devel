ISABELLE=isabelle
COMPCERTSSA_FILE=compcertSSA-2.0.tar.gz
COMPCERTSSA_URL="http://compcertssa.gforge.inria.fr/$(COMPCERTSSA_FILE)"
COMPCERTSSA_PATCH=compcertSSA-Braun.patch
COMPCERTSSA_TARGET=ia32-linux

.PHONY: clean all FormalSSA ifplot ccomp

all: compcertSSA/midend/SSA/BraunSSA.ml

$(COMPCERTSSA_FILE):
	wget -O $@ $(COMPCERTSSA_URL)

compcertSSA/.patched: $(COMPCERTSSA_FILE)
	tar --exclude=compcertSSA/tools/ndfun.[co]* --exclude=compcertSSA/doc/coq2html.o --exclude=compcertSSA/doc/coq2html.cm[xi] -xzf $(COMPCERTSSA_FILE)
	patch -p1 < $(COMPCERTSSA_PATCH)
	touch $@

compcertSSA/midend/SSA/BraunSSA.ml: $(wildcard *.thy) ROOT | compcertSSA/midend/SSA
	rm -f $@
	$(ISABELLE) build -c -d '$$AFP/Collections' -d '$$AFP/Refine_Monadic' -d '$$AFP/Automatic_Refinement' -d . compcertSSA
	ln -s ../../../BraunSSA.ml $@

compcertSSA/midend/SSA/ExternSSAgen.ml: compcertSSA/.patched

compcertSSA/midend/SSA:
	mkdir -p $@

compcertSSA/Makefile.config: compcertSSA/.patched
	cd compcertSSA;	./configure $(COMPCERTSSA_TARGET)

compcertSSA/ccomp: compcertSSA/Makefile.config compcertSSA/midend/SSA/ExternSSAgen.ml compcertSSA/midend/SSA/BraunSSA.ml
	$(MAKE) -C compcertSSA
	touch $@

test/ifgen: test/ifgen.c
	$(CC) -O2 -o $@ -std=c99 test/ifgen.c

ifplot: compcertSSA/ccomp test/ifplot.sh test/ifplot.gp test/ifgen
	seq 10 10 1000 | test/ifplot.sh
	gnuplot -p test/ifplot.gp


FormalSSA: compcertSSA/midend/SSA/BraunSSA.ml
ccomp: compcertSSA/ccomp

clean:
	rm -rf compcertSSA
	rm -f ifplot.data
	rm -f test/ifgen
	rm -f if.o
	rm -f $(COMPCERTSSA_FILE)
	isabelle build -c -n -d '$$AFP/Collections' -d '$$AFP/Refine_Monadic' -d '$$AFP/Automatic_Refinement' -d . compcertSSA ||:
