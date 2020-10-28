TARGET=Misc.vo Semiring.vo SRsummation.vo SRpolynomial.vo SRproduct.vo Matrix.vo BlockMat.vo deprecat_Ring2.vo
FILESFORDEP=`LC_ALL=C ls *.v`

all: pa_coq.cmo $(TARGET)

pa_coq.cmo: pa_coq.ml
	ocamlc -I $$(camlp5 -where) -pp camlp5r -c $<

clean:
	rm -f *.glob *.vo *.cm[iox] *.out *.o *.vok *.vos
	rm -f .*.bak .*.aux .*.cache

depend:
	mv .depend .depend.bak
	coqdep $(FILESFORDEP) | LC_ALL=C sort > .depend

.SUFFIXES: .v .vo

.v.vo:
	coqc $<

.PHONY: all clean depend

include .depend
