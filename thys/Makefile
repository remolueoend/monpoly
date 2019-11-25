ISABELLE=isabelle
afp=${AFP}

all: verimon

verimon:
	$(ISABELLE) build -d"${afp}/thys/" -evD .
	cp verified.ocaml ../src/verified.ml
