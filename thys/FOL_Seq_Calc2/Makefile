ISABELLE := .
ISABELLE_EXE := isabelle
HASKELL := haskell
EXPORT := $(HASKELL)/prover
APP := $(HASKELL)/app
LIB := $(HASKELL)/lib
ISABELLE_SOURCES = $(wildcard $(ISABELLE)/*.thy)

.PHONY: clean test

build: $(EXPORT)/%.hs
	cabal build

test:
	cabal test
	rm -rf test-tmp

$(EXPORT)/%.hs: $(ISABELLE_SOURCES) $(ISABELLE)/ROOT
	$(ISABELLE_EXE) export -d $(ISABELLE) -x "SeCaV_Prover*:**.hs" -p 3 -O $(EXPORT) SeCaV_Prover

clean:
	rm -rf $(EXPORT)
	rm -rf $(ISABELLE)/output
	cabal clean
