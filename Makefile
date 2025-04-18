all:
	cd ring_like; $(MAKE) $(MFLAGS)
	cd trigo_without_pi; $(MAKE) $(MFLAGS)
	cd sensitivity; $(MAKE) $(MFLAGS)
	cd rngl_alg; $(MAKE) $(MFLAGS)

clean:
	cd ring_like; $(MAKE) clean
	cd trigo_without_pi; $(MAKE) clean
	cd sensitivity; $(MAKE) clean
	cd rngl_alg; $(MAKE) clean

all1: ring_like trigo_without_pi sensitivity rngl_alg

ring_like:
	cd ring_like; $(MAKE) $(MFLAGS)

trigo_without_pi: ring_like
	cd trigo_without_pi; $(MAKE) $(MFLAGS)

sensitivity: ring_like
	cd sensitivity; $(MAKE) $(MFLAGS)

rngl_alg: trigo_without_pi sensitivity
	cd rngl_alg; $(MAKE) $(MFLAGS)

.PHONY: ring_like trigo_without_pi sensitivity rngl_alg
