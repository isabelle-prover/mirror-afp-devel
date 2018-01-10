ISABELLE=isabelle
GENERATED=generated
SRC=src
PROG=hlde

default: hlde

code: $(GENERATED)/HLDE.hs

$(GENERATED):
	@if [ ! -d $(GENERATED) ]; then mkdir $(GENERATED); fi

$(GENERATED)/$(PROG): $(GENERATED) $(SRC)/Main.hs
	$(ISABELLE) build -vd . HLDE

hlde: $(GENERATED)/$(PROG)
	@cp $(GENERATED)/$(PROG) $(PROG)

clean:
	rm -rf $(GENERATED)
	rm -f $(PROG)

.PHONY: code clean default hlde

