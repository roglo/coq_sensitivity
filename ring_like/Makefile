TARGET=RingLike.vo
FILESFORDEP=`LC_ALL=C ls *.v`

all: $(TARGET)

clean:
	rm -f *.glob *.vo *.cm[iox] *.out *.o *.vok *.vos
	rm -f .*.bak .*.aux .*.cache

depend:
	mv .depend .depend.bak
	coqdep $(FILESFORDEP) | LC_ALL=C sort > .depend | \
	sed -e 's/  *$$//' > .depend


.SUFFIXES: .v .vo

.v.vo:
	coqc -R . RingLike $<

.PHONY: all clean depend

include .depend
