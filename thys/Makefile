ISABELLE=isabelle
ifeq (${AFP},)
	p=$$AFP
else
	p=${AFP}/thys/
endif

all: verimon

verimon:
	$(ISABELLE) build -d'$p' -evD .
	cp verified.ocaml ../src/verified.ml
