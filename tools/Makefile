OCAMLOPT = ocamlopt
OCAMLC = ocamlc

# Set here which complier will be used
OCAML = $(OCAMLOPT)

FLAGS = -I ../src

ifeq "$(OCAML)" "$(OCAMLC)"
  O = cmo
  A = cma
  LIBS = -custom unix.$(A) str.$(A)
else
  O = cmx
  A = cmxa
  LIBS = unix.$(A) str.$(A) 
  OCAMLDEPFLAGS = -native
endif

OCAMLEXE = $(OCAML) $(FLAGS) $(LIBS)

MONPOLY_LIB = monpoly.$(A)

$(MONPOLY_LIB): 
	cd ../src && $(MAKE) $@

merger: $(MONPOLY_LIB) merger.ml
	$(OCAMLEXE) -I ../src/ ../src/$(MONPOLY_LIB) merger.ml -o $@

count: $(MONPOLY_LIB) count_events.ml
	$(OCAMLEXE) -I ../src/ ../src/$(MONPOLY_LIB) count_events.ml -o $@

fc_colsuf: $(MONPOLY_LIB) fc_colsuf.ml
	$(OCAMLEXE) -I ../src/ ../src/$(MONPOLY_LIB) fc_colsuf.ml -o $@

fc_paramslicing: $(MONPOLY_LIB) fc_paramslicing.ml
	$(OCAMLEXE) -I ../src/ ../src/$(MONPOLY_LIB) fc_paramslicing.ml -o $@

fc_filter_empty_tp: $(MONPOLY_LIB) fc_filter_empty_tp.ml
	$(OCAMLEXE) -I ../src/ ../src/$(MONPOLY_LIB) fc_filter_empty_tp.ml -o $@

compare: $(MONPOLY_LIB) compare_results.ml
	$(OCAMLEXE) -I ../src/ ../src/$(MONPOLY_LIB) compare_results.ml -o $@

mysql_test: $(MONPOLY_LIB) table2log.cmi table2log.$(O) mysql_test.ml
	$(OCAMLEXE) -I +mysql mysql.$(A) ../src/$(MONPOLY_LIB) table2log.$(O) mysql_test.ml -o $@

pgsql: $(MONPOLY_LIB) table2log.cmi table2log.$(O) pgsql.ml
	$(OCAMLEXE) -I +postgresql -thread threads.$(A) \
	bigarray.$(A) postgresql.$(A) ../src/$(MONPOLY_LIB) \
	table2log.$(O) pgsql.ml -o $@

pgsql_mon: $(MONPOLY_LIB) table2log.cmi table2log.$(O) pgsql_mon.ml
	$(OCAMLEXE) -I +postgresql -thread threads.$(A) \
	bigarray.$(A) postgresql.$(A) ../src/$(MONPOLY_LIB) \
	table2log.$(O) pgsql_mon.ml -o $@

mfotl2sql: $(MONPOLY_LIB) mfotl2sql.ml
	$(OCAMLEXE) -I ../src/ ../src/$(MONPOLY_LIB) mfotl2sql.ml -o $@

table2log: $(MONPOLY_LIB) table2log.cmi table2log.$(O)
	$(OCAMLEXE) -I ../src/ ../src/$(MONPOLY_LIB) table2log.ml -o $@

%.cmi: %.mli $(MONPOLY_LIB)
	$(OCAMLC) $(FLAGS) -c $<

%.cmo: %.ml $(MONPOLY_LIB) 
	$(OCAMLC) $(FLAGS) -c $<

%.cmx: %.ml $(MONPOLY_LIB) 
	$(OCAMLOPT) $(FLAGS) -c $<


clean:
	rm -f *.cm[iox]
