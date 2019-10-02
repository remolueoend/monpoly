BIN = ~/bin/
VER = 1.1.7
USERNAME ?= $(shell bash -c 'read -r -p "Username: " uuu; echo $$uuu')
IMAGENAME ?= $(shell bash -c 'read -r -p "Image name: " iii; echo $$iii')
ISABELLE=isabelle
export ISABELLE


all: monpoly

tools: merger fc_colsuf fc_paramslicing fc_filter_empty_tp compare count mfotl2sql table2log

.PHONY: monpoly doc clean clean-all depend 

monpoly: 
	cd src && $(MAKE) monpoly
	cp src/monpoly monpoly

verimon: isabelle clean
	cd src && $(MAKE) monpoly
	cp src/monpoly monpoly

isabelle: 
	cd thys && $(MAKE) verimon 
	cp thys/verified.ocaml src/verified.ml
	
merger: 
	cd tools && $(MAKE) merger

fc_colsuf: 
	cd tools && $(MAKE) fc_colsuf

fc_paramslicing: 
	cd tools && $(MAKE) fc_paramslicing

fc_filter_empty_tp: 
	cd tools && $(MAKE) fc_filter_empty_tp

compare: 
	cd tools && $(MAKE) compare

count: 
	cd tools && $(MAKE) count
	cp -v tools/count $(BIN)

mysql_test: 
	cd tools && $(MAKE) mysql_test
	cp -v tools/mysql_test $(BIN)

pgsql: 
	cd tools && $(MAKE) pgsql
	cp -v tools/pgsql_test $(BIN)

mfotl2sql: 
	cd tools && $(MAKE) mfotl2sql
	cp -v tools/mfotl2sql $(BIN)

table2log: 
	cd tools && $(MAKE) table2log
	cp -v tools/table2log $(BIN)

log_generator:
	cd tools && $(MAKE) log_generator
	cp tools/gen_log gen_log

fma_generator:
	cd src && $(MAKE) monpoly
	cd tools && $(MAKE) fma_generator
	cp tools/gen_fma gen_fma


install: monpoly 
	cp -v monpoly $(BIN)monpoly

install-all: install merger fc_colsuf fc_paramslicing fc_filter_empty_tp compare count mysql_test pgsql mfotl2sql table2log
	cp -v tools/merger $(BIN)
	cp -v tools/fc_colsuf $(BIN)
	cp -v tools/fc_paramslicing $(BIN)
	cp -v tools/fc_filter_empty_tp $(BIN)
	cp -v tools/compare $(BIN)
	cp -v tools/count $(BIN)
	cp -v tools/mysql_test $(BIN)
	cp -v tools/pgsql $(BIN)
	cp -v tools/mfotl2sql $(BIN)
	cp -v tools/table2log $(BIN)



doc: 
	cd src && $(MAKE) doc


clean: 
	cd src && $(MAKE) clean
	cd tools && $(MAKE) clean


clean-all: clean
	rm -f monpoly gen_fma gen_log
	rm -f doc/*
	rm -f tools/merger tools/fc_colsuf tools/fc_paramslicing tools/fc_filter_empty_tp tools/compare tools/count \
		tools/mysql_test tools/pgsql tools/mfotl2sql tools/table2log tools/gen_fma tools/gen_log
	rm -f src/monpoly $(BIN)monpoly $(BIN)mfotl2sql $(BIN)table2log

depend:
	cd src && $(MAKE) depend


monpoly-$(VER).tgz:
	tar --exclude=.svn -zcf ../monpoly-$(VER).tgz ../monpoly-$(VER)

release: monpoly-$(VER).tgz


docker: clean
	docker build -t $(USERNAME)/$(IMAGENAME) .

docker-run:
	docker run --name monpoly -it $(USERNAME)/$(IMAGENAME)

docker-push:
	docker login
	docker push $(USERNAME)/$(IMAGENAME)