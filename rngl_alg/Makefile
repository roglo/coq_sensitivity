TARGET=Qrl.vo Zrl.vo Nrl.vo QuadIntRl.vo
FILESFORDEP=`LC_ALL=C ls *.v`

all: $(TARGET)

pa_coq.cmo: pa_coq.ml
	ocamlc -I $$(camlp5 -where) -pp camlp5r -c $<

clean:
	rm -f *.glob *.vo *.cm[iox] *.out *.o *.vok *.vos
	rm -f .*.bak .*.aux .*.cache

depend:
	mv .depend .depend.bak
	coqdep -R ../main Main $(FILESFORDEP) | LC_ALL=C sort > .depend

.SUFFIXES: .v .vo

.v.vo:
	coqc -R ../main Main $<

.PHONY: all clean depend

include .depend
