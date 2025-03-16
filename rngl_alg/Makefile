TARGET=IntermVal.vo Qrl.vo Zrl.vo Nrl.vo MatRl.vo QuadIntRl.vo GaussIntRl.vo NewtonBinomial.vo AngleRl.vo Work3.vo AngleEuclDistLtAngleLtLt.vo Rrl.vo Ideal.vo QG.vo HyperbolicTrigo.vo AngleDeriv.vo AngleTan.vo
FILESFORDEP=`LC_ALL=C ls *.v`
QDIRS=-Q ../ring_like RingLike -Q ../main Main -Q ../trigo_without_pi Trigo
TEST_DIR=test `basename "$<"` = "$<" || { echo "File \"$<\" needs to be recompiled."; echo "Please run 'make' in directory '$$(dirname "$<")' first."; exit 1; }

all: $(TARGET)

pa_coq.cmo: pa_coq.ml
	ocamlc -I $$(camlp5 -where) -pp camlp5r -c $<

clean:
	rm -f *.glob *.vo *.cm[iox] *.out *.o *.vok *.vos
	rm -f .*.bak .*.aux .*.cache

depend:
	mv .depend .depend.bak
	coqdep $(QDIRS) $(FILESFORDEP) | LC_ALL=C sort | \
	sed -e 's/  *$$//' > .depend

.SUFFIXES: .v .vo

.v.vo:
	@$(TEST_DIR)
	coqc -R . RnglAlg $(QDIRS) $<

.PHONY: all clean depend

include .depend
