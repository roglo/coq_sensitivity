all: sensitivity rngl_alg

all1:
	cd sensitivity; $(MAKE) $(MFLAGS)
	cd rngl_alg; $(MAKE) $(MFLAGS)

depend:
	cd sensitivity; $(MAKE) depend
	cd rngl_alg; $(MAKE) depend

clean:
	cd sensitivity; $(MAKE) clean
	cd rngl_alg; $(MAKE) clean

sensitivity:
	cd sensitivity; $(MAKE) $(MFLAGS)

rngl_alg: sensitivity
	cd rngl_alg; $(MAKE) $(MFLAGS)

.PHONY: sensitivity rngl_alg
