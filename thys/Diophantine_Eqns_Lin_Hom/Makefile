ISABELLE=isabelle
GENERATED=generated
SRC=src
PROG=hlde
BUILD=build

default: hlde

code: $(GENERATED)/HLDE.hs

$(GENERATED):
	@if [ ! -d $(GENERATED) ]; then mkdir $(GENERATED); fi

$(GENERATED)/HLDE.hs: $(GENERATED)
	$(ISABELLE) build -vd . HLDE

hlde: $(GENERATED)/HLDE.hs $(SRC)/Main.hs
	@if [ ! -d $(BUILD) ]; then mkdir $(BUILD); fi
	@cp $(SRC)/Main.hs $(BUILD)/
	@echo "Copying generated source files into '$(BUILD)'"
	@cp $(GENERATED)/* $(BUILD)/
	@echo "Compiling sources"
	cd $(BUILD) && ghc --make Main -o $(PROG)
	@cp $(BUILD)/$(PROG) .

clean:
	rm -rf $(BUILD)

distclean:
	$(MAKE) clean
	rm -rf $(GENERATED)
	rm -f $(PROG)

.PHONY: code clean default hlde

