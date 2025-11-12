TARGET=Qrl.vo Nrl.vo MatRl.vo QuadIntRl.vo GaussIntRl.vo NewtonBinomial.vo AngleRl.vo Work3.vo AngleEuclDistLtAngleLtLt.vo Rrl.vo QG.vo HyperbolicTrigo.vo Rational.vo
FILESFORDEP=`LC_ALL=C ls *.v`
QDIRS=-Q ../sensitivity Sensitivity
TEST_DIR=test `basename "$<"` = "$<" || { echo "File \"$<\" needs to be recompiled."; echo "Please run 'make' in directory '$$(dirname "$<")' first."; exit 1; }
ROCQ=rocq compile
ROCQ_OPT=

all: $(TARGET)

pa_coq.cmo: pa_coq.ml
	ocamlc -I $$(camlp5 -where) -pp camlp5r -c $<

clean:
	rm -f *.glob *.vo *.cm[iox] *.out *.o *.vok *.vos
	rm -f .*.bak .*.aux .*.cache

depend:
	mv .depend .depend.bak
	rocq dep $(QDIRS) $(FILESFORDEP) | sed -e " s|$$HOME[^ ]*||" | \
	LC_ALL=C sort |	sed -e 's/  *$$//' > .depend

.SUFFIXES: .v .vo

%.vo: %.v
	@$(TEST_DIR)
	$(ROCQ) $(ROCQ_OPT) -R . RnglAlg $(QDIRS) $<

.PHONY: all clean depend

include .depend
