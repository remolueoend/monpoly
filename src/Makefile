OCAMLOPT = ocamlfind ocamlopt
OCAMLC = ocamlfind ocamlc

# Set here which complier will be used
OCAML = $(OCAMLOPT)
FLAGSLIB = -noassert -unsafe-string # -w A
FLAGS = -noassert -unsafe-string -package qcheck -package zarith -linkpkg -g # -w A
JSFLAGS = -package str -package unix -package js_of_ocaml -package lwt -package js_of_ocaml.syntax -syntax camlp4o
# FLAGS = -ccopt -static

ifeq "$(OCAML)" "$(OCAMLOPT)"
  O = cmx
  A = cmxa
  LIBS =  str.$(A) nums.$(A)
  OCAMLDEPFLAGS = -native
else
  O = cmo
  A = cma
  LIBS = -custom  str.$(A) nums.$(A)
endif

OCAMLEXE = $(OCAML) $(FLAGS) $(LIBS)


# The list of interface files
MLI = mqueue.mli dllist.mli misc.mli predicate.mli MFOTL.mli perf.mli \
      tuple.mli relation.mli table.mli db.mli \
      filter_rel.mli filter_empty_tp.mli sliding.mli \
	  helper.mli domain_set.mli extformula.mli mformula.mli marshalling.mli splitting.mli intmap.mli \
	  murmur_hash3.mli hypercube_slicer.mli rewriting.mli verified_adapter.mli

OURMLI = $(MLI) log.mli algorithm_verified.mli algorithm.mli

ALLMLI = $(OURMLI) formula_parser.mli log_parser.mli


# The lists of implementation files
OURML = $(OURMLI:.mli=.ml) verified.ml main.ml
ALLML = $(ALLMLI:.mli=.ml) formula_lexer.ml log_lexer.ml

# The lists of object files
OBJ =  verified.$(O) $(MLI:.mli=.$(O)) \
       formula_parser.$(O) log_parser.$(O) \
       formula_lexer.$(O) log_lexer.$(O) \
       log.$(O) algorithm.$(O) algorithm_verified.$(O)

OBJC = $(OBJ:.$(O)=.cmo)
OBJX = $(OBJ:.$(O)=.cmx)



# Targets
all: monpoly

monpoly: .depend $(OBJ) version.ml main.ml
	$(OCAMLEXE) $(OBJ) version.ml main.ml -o $@

monpoly.cma: .depend $(OBJC)
	$(OCAMLC) $(FLAGSLIB) -a $(OBJC) -o $@

monpoly.cmxa: .depend $(OBJX)
	$(OCAMLOPT) $(FLAGSLIB) -a $(OBJX) -o $@

monpoly.byte: .depend $(OBJC) version.ml main_js.ml
	$(OCAMLC) $(FLAGS) $(JSFLAGS) -linkpkg $(OBJC) version.ml main_js.ml -o $@

monpoly.js: monpoly.byte
	js_of_ocaml --disable genprim -I . --file examples:/ $<

profile: clean .depend version.ml main.ml
	ocamlbuild -use-ocamlfind -tag use_str -tag profile -package qcheck -package zarith main.native
	mv main.native monpoly

# update version with the latest revision number
version.ml: FORCE
	@echo "let ver = \"1.1.7 (`svnversion -cn`)\"" > version.ml
FORCE:


# Documentation
doc: $(OURMLI:.mli=.cmi)
	ocamldoc -html -d ../doc $(OURMLI)


# Clean-up
clean:
	rm -f .depend.init .depend
	rm -f *.cm[aiox] *.cmxa $(OBJ:.$(O)=.o) main.o version.o
	rm -f *parser.mli *parser.ml *lexer.ml version.ml
	rm -f *~


# Dependencies
%.cmi: %.mli
	$(OCAMLC) $(FLAGS) -c $<

%.cmo: %.ml
	$(OCAMLC) $(FLAGS) -c $<

%.cmx: %.ml
	$(OCAMLOPT) $(FLAGS) -c $<

%.ml: %.mll
	ocamllex $<

%.ml: %.mly
	ocamlyacc $<

%.mli: %.mly
	ocamlyacc $<

.depend: .depend.init $(ALLMLI) $(ALLML)
	ocamldep $(OCAMLDEPFLAGS) $(ALLMLI) $(ALLML) > .depend

.depend.init:
	ocamldep $(OCAMLDEPFLAGS) $(OURMLI) $(OURML) > .depend.init

depend: .depend

-include .depend











