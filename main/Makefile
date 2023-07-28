TARGET=Polynomial.vo CauchyBinet.vo Lemma_2_2.vo Lemma_2_1.vo Sensitivity.vo
FILESFORDEP=`LC_ALL=C ls *.v`

all: $(TARGET)

pa_coq.cmo: pa_coq.ml
	ocamlc -I $$(camlp5 -where) -pp camlp5r -c $<

clean:
	rm -f *.glob *.vo *.cm[iox] *.out *.o *.vok *.vos
	rm -f .*.bak .*.aux .*.cache

depend:
	mv .depend .depend.bak
	coqdep $(FILESFORDEP) | LC_ALL=C sort > .depend | \
	sed -e 's/  *$$//' > .depend


.SUFFIXES: .v .vo

.v.vo:
	coqc -R . Main -Q ../rngl_alg RnglAlg $<

.PHONY: all clean depend

include .depend
