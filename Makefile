all: ring_like trigo_without_pi sensitivity rngl_alg

all1:
	cd ring_like; $(MAKE) $(MFLAGS)
	cd trigo_without_pi; $(MAKE) $(MFLAGS)
	cd sensitivity; $(MAKE) $(MFLAGS)
	cd rngl_alg; $(MAKE) $(MFLAGS)

depend:
	cd ring_like; $(MAKE) depend
	cd trigo_without_pi; $(MAKE) depend
	cd sensitivity; $(MAKE) depend
	cd rngl_alg; $(MAKE) depend

clean:
	cd ring_like; $(MAKE) clean
	cd trigo_without_pi; $(MAKE) clean
	cd sensitivity; $(MAKE) clean
	cd rngl_alg; $(MAKE) clean

ring_like:
	cd ring_like; $(MAKE) $(MFLAGS)

trigo_without_pi: ring_like
	cd trigo_without_pi; $(MAKE) $(MFLAGS)

sensitivity: ring_like
	cd sensitivity; $(MAKE) $(MFLAGS)

rngl_alg: trigo_without_pi sensitivity
	cd rngl_alg; $(MAKE) $(MFLAGS)

.PHONY: ring_like trigo_without_pi sensitivity rngl_alg
