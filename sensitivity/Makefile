TARGET=Polynomial.vo CauchyBinet.vo Lemma_2_2.vo Lemma_2_1.vo Sensitivity.vo
FILESFORDEP=`LC_ALL=C ls *.v`
QDIRS=-Q ../ring_like RingLike
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
	$(ROCQ) $(ROCQ_OPTS) -R . Sensitivity -Q ../ring_like RingLike -Q ../rngl_alg RnglAlg $<

.PHONY: all clean depend

include .depend
